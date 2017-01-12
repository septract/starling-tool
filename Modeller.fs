/// <summary>
///     The main part of the converter from Starling's language AST to
///     its internal representation.
/// </summary>
module Starling.Lang.Modeller

open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Core.Traversal
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.ViewDesugar


/// <summary>
///     Types used only in the modeller and adjacent pipeline stages.
/// </summary>
[<AutoOpen>]
module Types =
    /// A conditional (flat or if-then-else) func.
    type CFunc =
        | ITE of SVBoolExpr * CView * CView
        | Func of SVFunc
        override this.ToString() = sprintf "CFunc(%A)" this

    /// A conditional view, or multiset of CFuncs.
    and CView = Multiset<IteratedContainer<CFunc, Sym<Var> option>>

    /// A partially resolved command.
    type PartCmd<'view> =
        | Prim of Starling.Core.Command.Types.Command
        | While of
            isDo : bool
            * expr : SVBoolExpr
            * inner : FullBlock<'view, PartCmd<'view>>
        | ITE of
            expr : SVBoolExpr
            * inTrue : FullBlock<'view, PartCmd<'view>>
            * inFalse : FullBlock<'view, PartCmd<'view>> option
        override this.ToString() = sprintf "PartCmd(%A)" this

    /// <summary>
    ///     Internal context for the method modeller.
    /// </summary>
    type MethodContext =
        { /// <summary>
          ///     The environment of visible shared variables.
          /// </summary>
          SharedVars : VarMap
          /// <summary>
          ///     The environment of visible thread-local variables.
          /// </summary>
          ThreadVars : VarMap
          /// <summary>
          ///     A definer containing the visible view prototypes.
          /// </summary>
          ViewProtos : FuncDefiner<ProtoInfo> }

    type ModellerViewExpr = ViewExpr<CView>
    type ModellerPartCmd = PartCmd<ModellerViewExpr>
    type ModellerBlock = FullBlock<ModellerViewExpr, PartCmd<ModellerViewExpr>>

    /// <summary>
    ///     A type, or maybe just a string description of one.
    /// </summary>
    type FuzzyType =
        /// <summary>A definite type.</summary>
        | Exact of Type
        /// <summary>A not so definite type.</summary>
        | Fuzzy of string

    /// <summary>
    ///     An error originating from the type system.
    /// </summary>
    type TypeError =
        /// <summary>
        ///     Two items that should have been the same type were not.
        ///     We know the expected type completely.
        /// </summary>
        | TypeMismatch of expected : FuzzyType * got : FuzzyType
        /// <summary>
        ///     A language type literal is inexpressible in Starling.
        /// </summary>
        | ImpossibleType of lit : TypeLiteral * why : string

    // TODO(CaptainHayashi): more consistent constructor names
    /// Represents an error when converting an expression.
    type ExprError =
        /// <summary>
        ///     The expression failed the type checker.
        /// </summary>
        | ExprBadType of err : TypeError
        /// <summary>
        ///     A variable in the expression failed the type checker.
        /// </summary>
        | VarBadType of var : Var * err : TypeError
        /// A variable usage in the expression produced a `VarMapError`.
        | Var of var : Var * err : VarMapError
        /// A substitution over the variable produced a `TraversalError`.
        | BadSub of err : TraversalError<unit>
        /// A symbolic expression appeared in an ambiguous position.
        | AmbiguousSym of sym : Symbolic<Expression>
        override this.ToString() = sprintf "%A" this

    /// Represents an error when converting a view prototype.
    type ViewProtoError =
        /// A parameter name was used more than once in the same view prototype.
        | VPEDuplicateParam of DesugaredViewProto * param : string
        /// <summary>
        ///     A view prototype had parameters of incorrect type in it.
        /// </summary>
        | BadParamType of proto : ViewProto * par : Param * err : TypeError

    /// Represents an error when converting a view or view def.
    type ViewError =
        /// An expression in the view generated an `ExprError`.
        | BadExpr of expr : AST.Types.Expression * err : ExprError
        /// A view was requested that does not exist.
        | NoSuchView of name : string
        /// A view lookup failed.
        | LookupError of name : string * err : Core.Definer.Error
        /// A view used variables in incorrect ways, eg by duplicating.
        | BadVar of err : VarMapError
        /// A viewdef conflicted with the shared variables.
        | SVarConflict of err : VarMapError
        override this.ToString () = sprintf "%A" this

    /// Represents an error when converting a constraint.
    type ConstraintError =
        /// The view definition in the constraint generated a `ViewError`.
        | CEView of vdef : AST.Types.ViewSignature * err : ViewError
        /// The expression in the constraint generated an `ExprError`.
        | CEExpr of expr : AST.Types.Expression * err : ExprError

    /// Represents an error when converting a prim.
    type PrimError =
        /// <summary>
        ///     A prim needed a lvalue but got a non-lvalue expression.
        /// </summary>
        | NeedLValue of expr : AST.Types.Expression
        /// A prim contained a bad expression.
        | BadExpr of expr : AST.Types.Expression * err : ExprError
        /// A prim tried to increment an expression.
        | IncExpr of expr : AST.Types.Expression
        /// A prim tried to decrement an expression.
        | DecExpr of expr : AST.Types.Expression
        /// A prim tried to increment a Boolean.
        | IncBool of expr : AST.Types.Expression
        /// A prim tried to decrement a Boolean.
        | DecBool of expr : AST.Types.Expression
        /// A prim tried to atomic-load from a non-lvalue expression.
        | LoadNonLV of expr : AST.Types.Expression
        /// A prim has no effect.
        | Useless
        /// <summary>A prim is not yet implemented in Starling.</summary>
        | PrimNotImplemented of what : string
        /// <summary>Handling variables in symbolic prims caused an error.</summary>
        | SymVarError of err : VarMapError

    /// Represents an error when converting a method.
    type MethodError =
        /// The method contains a semantically invalid local assign.
        | BadAssign of dest : AST.Types.Expression
                     * src : AST.Types.Expression
                     * err : PrimError
        /// The method contains a semantically invalid atomic action.
        | BadAtomic of atom : Atomic * err : PrimError
        /// The method contains a bad if-then-else condition.
        | BadITECondition of expr: AST.Types.Expression * err: ExprError
        /// The method contains a bad while condition.
        | BadWhileCondition of expr: AST.Types.Expression * err: ExprError
        /// The method contains a bad view.
        | BadView of view : ViewExpr<AST.Types.View> * err : ViewError
        /// The method contains an command not yet implemented in Starling.
        | CommandNotImplemented of cmd : FullCommand

    /// Represents an error when converting a model.
    type ModelError =
        /// A view prototype in the program generated a `ViewProtoError`.
        | BadVProto of proto : DesugaredViewProto * err : ViewProtoError
        /// A view prototype's parameter in the program generated a `TypeError`.
        | BadVProtoParamType of proto : ViewProto * param : Param * err : TypeError
        /// A constraint in the program generated a `ConstraintError`.
        | BadConstraint of constr : AST.Types.ViewSignature * err : ConstraintError
        /// A method in the program generated an `MethodError`.
        | BadMethod of methname : string * err : MethodError
        /// A variable in the program generated a `VarMapError`.
        | BadVar of scope: string * err : VarMapError
        /// A variable declaration in the program generated a `TypeError`.
        | BadVarType of var: string * err : TypeError

/// <summary>
///     Pretty printers for the modeller types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Collections.Multiset.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Traversal.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.View.Pretty
    open Starling.Lang.AST.Pretty
    open Starling.Lang.ViewDesugar.Pretty

    /// Pretty-prints a CFunc.
    let rec printCFunc : CFunc -> Doc =
        function
        | CFunc.ITE(i, t, e) ->
            hsep [ String "if"
                   printSVBoolExpr i
                   String "then"
                   t |> printCView |> ssurround "[" "]"
                   String "else"
                   e |> printCView |> ssurround "[" "]" ]
        | Func v -> printSVFunc v

    /// Pretty-prints a CView.
    and printCView : CView -> Doc =
        printMultiset
            (printIteratedContainer printCFunc (maybe Nop (printSym printVar)))
        >> ssurround "[|" "|]"

    /// Pretty-prints a part-cmd at the given indent level.
    let rec printPartCmd (pView : 'view -> Doc) (pc : PartCmd<'view>) : Doc =
        let pfb = printFullBlock pView (printPartCmd pView)
        match pc with
        | PartCmd.Prim prim -> Command.Pretty.printCommand prim
        | PartCmd.While(isDo, expr, inner) ->
            cmdHeaded (hsep [ String(if isDo then "Do-while" else "While")
                              (printSVBoolExpr expr) ])
                      [ pfb inner ]
        | PartCmd.ITE(expr, inTrue, inFalse) ->
            cmdHeaded (hsep [ String "begin if"; printSVBoolExpr expr ])
                      [ headed "True" [ pfb inTrue ]
                        maybe Nop (fun f -> headed "False" [ pfb f]) inFalse ]

    /// <summary>
    ///     Pretty-prints fuzzy type identifiers.
    /// </summary>
    /// <param name="ft">The fuzzy type to print.</param>
    /// <returns>
    ///     A pretty-printer command that prints <paramref name="ft" />.
    /// </returns>
    let printFuzzyType (ft : FuzzyType) : Doc =
        match ft with
        | Fuzzy descr -> String descr
        | Exact ty -> quoted (printType ty)

    /// <summary>
    ///     Pretty-prints type errors.
    /// </summary>
    /// <param name="err">The error to print.</param>
    /// <returns>
    ///     A pretty-printer command that prints <paramref name="err" />.
    /// </returns>
    let printTypeError (err : TypeError) : Doc =
        match err with
        | TypeMismatch (expected, got) ->
            errorStr "expected"
            <+> error (printFuzzyType expected)
            <&> errorStr "got"
            <+> error (printFuzzyType got)
        | ImpossibleType (lit, why) ->
            let header =
                errorStr "type literal"
                <+> quoted (printTypeLiteral lit)
                <&> errorStr "cannot be expressed in Starling"
            cmdHeaded header [ errorInfoStr why ]

    /// <summary>
    ///     Pretty-prints expression conversion errors.
    /// </summary>
    /// <param name="err">The error to print.</param>
    /// <returns>
    ///     A pretty-printer command that prints <paramref name="err" />.
    /// </returns>
    let printExprError (err : ExprError) : Doc =
        match err with
        | ExprBadType err ->
            cmdHeaded (errorStr "type error in expression")
                [ printTypeError err ]
        | VarBadType (lv, err) ->
            let header =
                errorStr "type error in variable" <+> quoted (String lv)
            cmdHeaded header [ printTypeError err ]
        | Var(var, err) -> wrapped "variable" (var |> String) (err |> printVarMapError)
        | BadSub err ->
            fmt "Substitution error: {0}" [ printTraversalError (fun _ -> String "()") err ]
        | AmbiguousSym sym ->
            fmt
                "symbolic var '{0}' has ambiguous type: \
                 place it inside an expression with non-symbolic components"
                [ printSymbolic sym ]

    /// Pretty-prints view conversion errors.
    let printViewError : ViewError -> Doc =
        function
        | ViewError.BadExpr(expr, err) ->
            wrapped "expression" (printExpression expr) (printExprError err)
        | NoSuchView name -> fmt "no view prototype for '{0}'" [ String name ]
        | LookupError(name, err) ->
            wrapped "lookup for view"
                (String name)
                (Definer.Pretty.printError err)
        | ViewError.BadVar err ->
            colonSep [ "invalid variable usage" |> String
                       err |> printVarMapError ]
        | SVarConflict err ->
            colonSep [ "parameters conflict with shared variables" |> String
                       err |> printVarMapError ]

    /// Pretty-prints constraint conversion errors.
    let printConstraintError : ConstraintError -> Doc =
        function
        | CEView(vdef, err) ->
            wrapped "view definition" (printViewSignature vdef) (printViewError err)
        | CEExpr(expr, err) ->
            wrapped "expression" (printExpression expr) (printExprError err)

    /// Pretty-prints view prototype conversion errors
    let printViewProtoError : ViewProtoError -> Doc =
        function
        | VPEDuplicateParam(vp, param) ->
            fmt "view proto '{0}' has duplicate param {1}"
                [ printGeneralViewProto printTypedVar vp; String param ]
        | BadParamType (proto, par, err) ->
            cmdHeaded
                (errorStr "parameter"
                 <+> quoted (printParam par)
                 <+> errorStr "in view proto"
                 <+> quoted (printGeneralViewProto printParam proto)
                 <+> errorStr "has bad type")
                [ printTypeError err ]

    /// Pretty-prints prim errors.
    let printPrimError (err : PrimError) : Doc =
        match err with
        | NeedLValue expr ->
            errorStr "expected lvalue here, but got"
            <+> quoted (printExpression expr)
        | BadExpr (expr, err : ExprError) ->
            wrapped "expression" (printExpression expr)
                                 (printExprError err)
        | IncExpr expr ->
            fmt "cannot increment an expression ('{0}')"
                [ printExpression expr ]
        | DecExpr expr ->
            fmt "cannot decrement an expression ('{0}')"
                [ printExpression expr ]
        | IncBool expr ->
            fmt "cannot increment a Boolean ('{0}')"
                [ printExpression expr ]
        | DecBool expr ->
            fmt "cannot decrement a Boolean ('{0}')"
                [ printExpression expr ]
        | LoadNonLV expr ->
            fmt "cannot load from non-lvalue expression '{0}'"
                [ printExpression expr ]
        | Useless -> String "command has no effect"
        | PrimNotImplemented what ->
            errorStr "primitive command"
            <+> quoted (String what)
            <+> errorStr "not yet implemented"
        | SymVarError err ->
            errorStr "error in translating symbolic command"
            <&> printVarMapError err

    /// Pretty-prints method errors.
    let printMethodError (err : MethodError) : Doc =
        match err with
        | BadAssign (dest, src, err) ->
            wrapped "local assign" (printAssign dest src) (printPrimError err)
        | BadAtomic (atom, err) ->
            wrapped "atomic action" (printAtomic atom) (printPrimError err)
        | BadITECondition (expr, err) ->
            wrapped "if-then-else condition" (printExpression expr)
                                             (printExprError err)
        | BadWhileCondition (expr, err) ->
            wrapped "while-loop condition" (printExpression expr)
                                           (printExprError err)
        | BadView (view, err) ->
            wrapped "view expression" (printViewExpr printView view)
                                      (printViewError err)
        | CommandNotImplemented cmd ->
            fmt "command {0} not yet implemented" [ printFullCommand cmd ]

    /// Pretty-prints model conversion errors.
    let printModelError (err : ModelError) : Doc =
        match err with
        | BadConstraint(constr, err) ->
            wrapped "constraint" (printViewSignature constr)
                                 (printConstraintError err)
        | BadVar(scope, err) ->
            wrapped "variables in scope" (String scope) (printVarMapError err)
        | BadMethod(methname, err) ->
            wrapped "method" (String methname) (printMethodError err)
        | BadVProto(vproto, err) ->
            wrapped "view prototype" (printGeneralViewProto printTypedVar vproto)
                                     (printViewProtoError err)
        | BadVProtoParamType(vproto, param, err) ->
            let head =
                errorStr "type of param"
                <+> quoted (printParam param)
                <+> errorStr "in view prototype"
                <+> quoted (printGeneralViewProto printParam vproto)
            cmdHeaded head [ printTypeError err ]
        | BadVarType(name, err) ->
            wrapped "type of variable" (String name) (printTypeError err)


(*
 * Starling imperative language semantics
 *)

/// Creates a prim from a name, results list, and arguments list.
let mkPrim (name : string) (results : TypedVar list) (args : TypedVar list)
  (body : Microcode<TypedVar, Var> list)
  : PrimSemantics =
    { Name = name; Results = results; Args = args; Body = body }


/// <summary>
///   The core semantic function for the imperative language.
/// </summary>
/// <remarks>
///   <para>
///     The functions beginning with '!' have special syntax in the
///     imperative language.
///   </para>
/// </remarks>
let coreSemantics : PrimSemanticsMap =
    // TODO(CaptainHayashi): specify this in the language (standard library?).
    // TODO(CaptainHayashi): generic functions?
    // TODO(CaptainHayashi): add shared/local/expr qualifiers to parameters?
    List.fold (fun m (a : PrimSemantics) -> Map.add a.Name a m) Map.empty
    <| [
      (*
       * CAS
       *)
      (mkPrim "ICAS" [ normalIntVar "destA"; normalIntVar "testA" ] [ normalIntVar "destB"; normalIntVar "testB"; normalIntVar "set" ]
           [ Branch
                (iEq (IVar "destB") (IVar "testB"),
                 [ normalIntVar "destA" *<- normalIntExpr (IVar "set")
                   normalIntVar "testA" *<- normalIntExpr (IVar "testB") ],
                 [ normalIntVar "destA" *<- normalIntExpr (IVar "destB")
                   normalIntVar "testA" *<- normalIntExpr (IVar "destB") ] ) ] )
      // Boolean CAS
      (mkPrim "BCAS" [ normalBoolVar "destA"; normalBoolVar "testA" ] [ normalBoolVar "destB"; normalBoolVar "testB"; normalBoolVar "set" ]
           [ Branch
                (bEq (BVar "destB") (BVar "testB"),
                 [ normalBoolVar "destA" *<- normalBoolExpr (BVar "set")
                   normalBoolVar "testA" *<- normalBoolExpr (BVar "testB") ],
                 [ normalBoolVar "destA" *<- normalBoolExpr (BVar "destB")
                   normalBoolVar "testA" *<- normalBoolExpr (BVar "destB") ] ) ] )
      (*
       * Atomic load
       *)
      // Integer load
      (mkPrim "!ILoad"  [ normalIntVar "dest" ] [ normalIntVar "src" ]
            [ normalIntVar "dest" *<- normalIntExpr (IVar "src") ] )

      // Integer load-and-increment
      (mkPrim "!ILoad++"  [ normalIntVar "dest"; normalIntVar "srcA" ] [ normalIntVar "srcB" ]
            [ normalIntVar "dest" *<- normalIntExpr (IVar "srcB")
              normalIntVar "srcA" *<- normalIntExpr (mkAdd2 (IVar "srcB") (IInt 1L)) ] )

      // Integer load-and-decrement
      (mkPrim "!ILoad--"  [ normalIntVar "dest"; normalIntVar "srcA" ] [ normalIntVar "srcB" ]
            [ normalIntVar "dest" *<- normalIntExpr (IVar "srcB")
              normalIntVar "srcA" *<- normalIntExpr (mkSub2 (IVar "srcB") (IInt 1L)) ] )

      // Integer increment
      (mkPrim "!I++"  [ normalIntVar "srcA" ] [ normalIntVar "srcB" ]
            [ normalIntVar "srcA" *<- normalIntExpr (mkAdd2 (IVar "srcB") (IInt 1L)) ] )

      // Integer decrement
      (mkPrim "!I--"  [ normalIntVar "srcA" ] [ normalIntVar "srcB" ]
            [ normalIntVar "srcA" *<- normalIntExpr (mkSub2 (IVar "srcB") (IInt 1L)) ] )

      // Boolean load
      (mkPrim "!BLoad"  [ normalBoolVar "dest" ] [ normalBoolVar "src" ]
            [ normalBoolVar "dest" *<- normalBoolExpr (BVar "src") ] )

      (*
       * Atomic store
       *)

      // Integer store
      (mkPrim "!IStore" [ normalIntVar "dest" ] [ normalIntVar "src" ]
            [ normalIntVar "dest" *<- normalIntExpr (IVar "src") ] )

      // Boolean store
      (mkPrim "!BStore" [ normalBoolVar "dest" ] [ normalBoolVar "src" ]
            [ normalBoolVar "dest" *<- normalBoolExpr (BVar "src") ] )

      (*
       * Local set
       *)

      // Integer local set
      (mkPrim "!ILSet" [ normalIntVar "dest" ] [ normalIntVar "src" ]
            [ normalIntVar "dest" *<- normalIntExpr (IVar "src") ] )

      // Boolean store
      (mkPrim "!BLSet" [ normalBoolVar "dest" ] [ normalBoolVar "src" ]
            [ normalBoolVar "dest" *<- normalBoolExpr (BVar "src") ] )

      (*
       * Assumptions
       *)

      // Identity
      (mkPrim "Id" [] [] [])

      // Assume
      (mkPrim "Assume" [] [normalBoolVar "expr"] [ Microcode.Assume (BVar "expr") ]) ]

(*
 * Expression translation
 *)

/// <summary>
///     Constructs an expression-level type mismatch error.
/// </summary>
/// <param name="expected">The expected type of the expression.</param>
/// <param name="got">The actual type of the expression.</param>
/// <returns>An <see cref="ExprError"/> representing a type mismatch.</returns>
let exprTypeMismatch (expected : FuzzyType) (got : FuzzyType) : ExprError =
    ExprBadType (TypeMismatch (expected = expected, got = got))

/// <summary>
///     Constructs a primitive-level expression type mismatch error.
/// </summary>
/// <param name="expr">The AST of the expression being modelled.</param>
/// <param name="expected">The expected type of the expression.</param>
/// <param name="got">The actual type of the expression.</param>
/// <returns>An <see cref="PrimError"/> representing a type mismatch.</returns>
let primTypeMismatch
  (expr : Expression) (expected : FuzzyType) (got : FuzzyType) : PrimError =
    BadExpr (expr, exprTypeMismatch expected got)

// <summary>
//     Given a subtyped integer expression, check whether it can be used as a
//     'normal'-typed integer expression.
//
//     <para>
//         This is used whenever integer expressions need to be used as
//         indices to arrays.
//     </para>
// </summary>
// <param name="int">The integer to check for type compatibility.</param>
// <typeparam name="Var">The type of variables in the expression.</typeparm>
// <returns>
//     If the expression is compatible with 'int', the modelled expression.
//     Else, a type error.
// </returns>
let checkIntIsNormalType (int : TypedIntExpr<'Var>)
  : Result<IntExpr<'Var>, TypeError> =
    if primTypeRecsCompatible int.SRec normalRec
    then ok int.SExpr
    else
        fail
            (TypeMismatch
                (expected = Exact (Typed.Int (normalRec, ())),
                 got = Exact (Typed.Int (int.SRec, ()))))

// <summary>
//     Given a subtyped Boolean expression, check whether it can be used as a
//     'normal'-typed Boolean expression.
//
//     <para>
//         This is used whenever Boolean expressions need to be used as
//         predicates, ie as view conditions or view definitions.
//     </para>
// </summary>
// <param name="bool">The Boolean to check for type compatibility.</param>
// <typeparam name="Var">The type of variables in the expression.</typeparm>
// <returns>
//     If the expression is compatible with 'bool', the modelled expression.
//     Else, a type error.
// </returns>
let checkBoolIsNormalType (bool : TypedBoolExpr<'Var>)
  : Result<BoolExpr<'Var>, TypeError> =
    if primTypeRecsCompatible bool.SRec normalRec
    then ok bool.SExpr
    else
        fail
            (TypeMismatch
                (expected = Exact (Typed.Bool (normalRec, ())),
                 got = Exact (Typed.Bool (bool.SRec, ()))))


/// <summary>
///     Models a Starling expression as an <c>Expr</c>.
///
///     <para>
///         Whenever we find a variable, we check the given environment
///         to make sure it both exists and is being used in a type-safe
///         manner.  Thus, this part of the modeller implements much of
///         Starling's type checking.
///     </para>
///     <para>
///         Since <c>modelExpr</c> and its Boolean and integral
///         equivalents are used to create expressions over both
///         <c>Var</c> and <c>MarkedVar</c>, we allow variable lookups
///         to be modified by a post-processing function.
///     </para>
/// </summary>
/// <param name="env">
///     The <c>VarMap</c> of variables bound where this expression
///     occurs.  Usually, but not always, these are the thread-local
///     variables.
/// </param>
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in the modelled expression.  Use this
///     to apply markers on variables, etc.
/// </param>
/// <param name="idxEnv">
///     The <c>VarMap</c> of variables available to any array subscripts in this
///     expression.  This is almost always the thread-local variables.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>Expr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A function taking <c>Expression</c>s.  This function will return
///     a <c>Result</c>, over <c>ExprError</c>, containing the modelled
///     <c>Expr</c> on success.  The exact type parameters of the
///     expression depend on <paramref name="varF"/>.
/// </returns>
let rec modelExpr
  (env : VarMap)
  (idxEnv : VarMap)
  (varF : Var -> 'var)
  (e : Expression)
  : Result<Expr<Sym<'var>>, ExprError> =
    match e.Node with
        (* First, if we have a variable, the type of expression is
           determined by the type of the variable.  If the variable is
           symbolic, then we have ambiguity. *)
        | Identifier v ->
            bind
                (liftWithoutContext
                    (varF >> Reg >> ok)
                    (tliftOverCTyped >> tliftToExprDest)
                 >> mapMessages BadSub)
                (wrapMessages Var (VarMap.lookup env) v)
        | Symbolic sym ->
            fail (AmbiguousSym sym)
        (* If we have an array, then work out what the type of the array's
           elements are, then walk back from there. *)
        | ArraySubscript (arr, idx) ->
            let arrR = modelArrayExpr env idxEnv varF arr
            // Indices always have to be of type 'int'.
            let idxuR = modelIntExpr idxEnv idxEnv varF idx
            let idxR = bind (checkIntIsNormalType >> mapMessages ExprBadType) idxuR

            lift2
                (fun arrE idxE ->
                    match arrE.SRec.ElementType with
                    | AnIntR r -> Expr.Int (r, IIdx (arrE, idxE))
                    | ABoolR r -> Expr.Bool (r, BIdx (arrE, idxE))
                    | AnArrayR r -> Expr.Array (r, AIdx (arrE, idxE)))
                arrR idxR
        (* We can use the active patterns above to figure out whether we
         * need to treat this expression as arithmetic or Boolean.
         *)
        | ArithExp' _ -> lift (liftTypedSub Expr.Int) (modelIntExpr env idxEnv varF e)
        | BoolExp' _ -> lift (liftTypedSub Expr.Bool) (modelBoolExpr env idxEnv varF e)
        | _ -> failwith "unreachable[modelExpr]"

/// <summary>
///     Models a Starling Boolean expression as a <c>BoolExpr</c>.
///
///     <para>
///         See <c>modelExpr</c> for more information.
///     </para>
/// </summary>
/// <param name="env">
///     The <c>VarMap</c> of variables bound where this expression
///     occurs.  Usually, but not always, these are the thread-local
///     variables.
/// </param>
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in <c>IVar</c>.  Use this to apply
///     markers on variables, etc.
/// </param>
/// <param name="expr">
///     An expression previously judged as Boolean, to be modelled.
/// </param>
/// <param name="idxEnv">
///     The <c>VarMap</c> of variables available to any array subscripts in this
///     expression.  This is almost always the thread-local variables.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>BoolExpr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A <c>Result</c>, over <c>ExprError</c>, containing the modelled
///     <c>BoolExpr</c> on success.
///     The exact type parameters of the expression depend on
///     <paramref name="varF"/>.
/// </returns>
and modelBoolExpr
  (env : VarMap)
  (idxEnv : VarMap)
  (varF : Var -> 'var)
  (expr : Expression) : Result<TypedBoolExpr<Sym<'var>>, ExprError> =
    let mi = modelIntExpr env idxEnv varF
    let me = modelExpr env idxEnv varF
    let ma = modelArrayExpr env idxEnv varF

    let rec mb e : Result<TypedBoolExpr<Sym<'var>>, ExprError> =
        match e.Node with
        // These two have a indefinite subtype.
        | True -> ok (indefBool BTrue)
        | False -> ok (indefBool BFalse)
        | Identifier v ->
            (* Look-up the variable to ensure it a) exists and b) is of a
             * Boolean type.
             *)
            bind
                (function
                 | Typed.Bool (t, vn) ->
                     ok (mkTypedSub t (BVar (Reg (varF vn))))
                 | vr ->
                    fail
                        (VarBadType
                            (v,
                             TypeMismatch
                                (expected = Fuzzy "bool", got = Exact (typeOf vr)))))
                (wrapMessages Var (VarMap.lookup env) v)
        | Symbolic { Sentence = sen; Args = args } ->
            // Symbols have an indefinite subtype.
            args
            |> List.map me
            |> collect
            |> lift (fun a -> indefBool (BVar (Sym { Sentence = sen; Args = a })))
        | ArraySubscript (arr, idx) ->
            let arrR = ma arr
            // Indices always have to be of type 'int'.
            // Bind array index using its own environment.
            let idxuR = modelIntExpr idxEnv idxEnv varF idx
            let idxR = bind (checkIntIsNormalType >> mapMessages ExprBadType) idxuR

            bind2
                (fun arrE idxE ->
                    match arrE.SRec.ElementType with
                    | ABoolR r -> ok (mkTypedSub r (BIdx (arrE, idxE)))
                    | t -> fail (exprTypeMismatch (Fuzzy "bool[]") (Exact t)))
                arrR idxR
        | BopExpr(BoolOp as op, l, r) ->
            match op with
            | ArithIn as o ->
                let oper =
                    match o with
                    | Gt -> mkGt
                    | Ge -> mkGe
                    | Le -> mkLe
                    | Lt -> mkLt
                    | _ -> failwith "unreachable[modelBoolExpr::ArithIn]"
                // We don't know the subtype of this yet...
                lift indefBool (lift2 oper (mi l) (mi r))
            | BoolIn as o ->
                let oper =
                    match o with
                    | And -> mkAnd2
                    | Or -> mkOr2
                    | Imp -> mkImpl
                    | _ -> failwith "unreachable[modelBoolExpr::BoolIn]"

                (* Both sides of the expression need to be unifiable to the
                   same type. *)
                bind2
                    (fun ml mr ->
                        match unifyPrimTypeRecs [ ml.SRec; mr.SRec ] with
                        | Some t ->
                            ok (mkTypedSub t (oper (stripTypeRec ml) (stripTypeRec mr)))
                        | None ->
                            fail
                                (ExprBadType
                                    (TypeMismatch
                                        (expected = Exact (Type.Bool (ml.SRec, ())),
                                         got = Exact (Type.Bool (mr.SRec, ()))))))
                    (mb l)
                    (mb r)
            | AnyIn as o ->
                let oper =
                    match o with
                    | Eq -> mkEq
                    | Neq -> mkNeq
                    | _ -> failwith "unreachable[modelBoolExpr::AnyIn]"
                // We don't know the subtype of this yet...
                lift indefBool (lift2 oper (me l) (me r))
        | UopExpr (Neg,e) -> lift (mapTypedSub mkNot) (mb e) 
        | _ ->
            fail
                (ExprBadType
                    (TypeMismatch (expected = Fuzzy "bool", got = Fuzzy "unknown non-bool")))
    mb expr

/// <summary>
///     Models a Starling integral expression as an <c>IntExpr</c>.
///
///     <para>
///         See <c>modelExpr</c> for more information.
///     </para>
/// </summary>
/// <param name="env">
///     The <c>VarMap</c> of variables bound where this expression
///     occurs.  Usually, but not always, these are the thread-local
///     variables.
/// </param>
/// <param name="idxEnv">
///     The <c>VarMap</c> of variables available to any array subscripts in this
///     expression.  This is almost always the thread-local variables.
/// </param>
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in <c>IVar</c>.  Use this to apply
///     markers on variables, etc.
/// </param>
/// <param name="expr">
///     An expression previously judged as integral, to be modelled.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>IntExpr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A <c>Result</c>, over <c>ExprError</c>, containing the modelled
///     <c>IntExpr</c> on success.
///     The exact type parameters of the expression depend on
///     <paramref name="varF"/>.
/// </returns>
and modelIntExpr
  (env : VarMap)
  (idxEnv : VarMap)
  (varF : Var -> 'var)
  (expr : Expression) : Result<TypedIntExpr<Sym<'var>>, ExprError> =
    let me = modelExpr env idxEnv varF
    let ma = modelArrayExpr env idxEnv varF

    let rec mi e =
        match e.Node with
        // Numbers have indefinite subtype.
        | Num i -> ok (indefInt (IInt i))
        | Identifier v ->
            (* Look-up the variable to ensure it a) exists and b) is of an
             * arithmetic type.
             *)
            v
            |> wrapMessages Var (VarMap.lookup env)
            |> bind (function
                     | Typed.Int (ty, vn) ->
                         ok (mkTypedSub ty (IVar (Reg (varF vn))))
                     | vr ->
                        fail
                            (VarBadType
                                (v,
                                 TypeMismatch
                                    (expected = Fuzzy "int", got = Exact (typeOf vr)))))
         | Symbolic { Sentence = sen; Args = args } ->
            // Symbols have indefinite subtype.
            args
            |> List.map me
            |> collect
            |> lift (fun a -> indefInt (IVar (Sym { Sentence = sen; Args = a })))
        | ArraySubscript (arr, idx) ->
            let arrR = ma arr
            // Indices always have to be of type 'int'.
            // Bind array index using its own environment.
            let idxuR = modelIntExpr idxEnv idxEnv varF idx
            let idxR = bind (checkIntIsNormalType >> mapMessages ExprBadType) idxuR

            bind2
                (fun arrE idxE ->
                    match arrE.SRec.ElementType with
                    | AnIntR ty -> ok (mkTypedSub ty (IIdx (arrE, idxE)))
                    | t -> fail (exprTypeMismatch (Fuzzy "int[]") (Exact (typeOf (liftTypedSub Array arrE)))))
                arrR idxR
        | BopExpr(ArithOp as op, l, r) ->
            let oper =
                match op with
                | Mul -> mkMul2
                | Mod -> mkMod
                | Div -> mkDiv
                | Add -> mkAdd2
                | Sub -> mkSub2
                | _ -> failwith "unreachable[modelIntExpr]"

            bind2
                (fun ll lr ->
                    (* We need to make sure that 'll' 'lr' have compatible inner
                       type by unifying their extended type records. *)
                    match unifyPrimTypeRecs [ ll.SRec; lr.SRec ] with
                    | Some srec ->
                        ok (mkTypedSub srec (oper (stripTypeRec ll) (stripTypeRec lr)))
                    | None ->
                        fail
                            (ExprBadType
                                (TypeMismatch
                                    (expected = Exact (typeOf (liftTypedSub Int ll)),
                                     got = Exact (typeOf (liftTypedSub Int lr))))))
                (mi l) (mi r)
        | _ -> fail (exprTypeMismatch (Fuzzy "int") (Fuzzy "unknown non-int"))
    mi expr

/// <summary>
///     Models a Starling array expression as an <c>ArrayExpr</c>.
///
///     <para>
///         See <c>modelExpr</c> for more information.
///     </para>
/// </summary>
/// <param name="env">
///     The <c>VarMap</c> of variables bound where this expression
///     occurs.  Usually, but not always, these are the thread-local
///     variables.
/// </param>
/// <param name="idxEnv">
///     The <c>VarMap</c> of variables available to any array subscripts in this
///     expression.  This is almost always the thread-local variables.
/// </param>
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in <c>AVar</c>.  Use this to apply
///     markers on variables, etc.
/// </param>
/// <param name="expr">
///     An expression previously judged as integral, to be modelled.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>ArrayExpr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A <c>Result</c>, over <c>ExprError</c>, containing the modelled
///     <c>ArrayExpr</c> on success.
///     The exact type parameters of the expression depend on
///     <paramref name="varF"/>.
/// </returns>
and modelArrayExpr
  (env : VarMap)
  (idxEnv : VarMap)
  (varF : Var -> 'var)
  (expr : Expression)
  : Result<TypedArrayExpr<Sym<'var>>, ExprError> =
    let mi = modelIntExpr env idxEnv varF

    let rec ma e =
        match e.Node with
        | Identifier v ->
            (* Look-up the variable to ensure it a) exists and b) is of an
             * array type.
             *)
            v
            |> wrapMessages Var (VarMap.lookup env)
            |> bind (function
                     | Typed.Array (t, vn) ->
                        ok (mkTypedSub t (AVar (Reg (varF vn))))
                     | vr ->
                        fail
                            (VarBadType
                                (v,
                                 TypeMismatch
                                    (expected = Fuzzy "array", got = Exact (typeOf vr)))))
        | Symbolic sym ->
            (* TODO(CaptainHayashi): a symbolic array is ambiguously typed.
               Maybe when modelling we should take our 'best guess' at
               eltype and length from any subscripting expression? *)
            fail (AmbiguousSym sym)
        | ArraySubscript (arr, idx) ->
            let arrR = ma arr
            // Indices always have to be of type 'int'.
            let idxuR = modelIntExpr idxEnv idxEnv varF idx
            let idxR = bind (checkIntIsNormalType >> mapMessages ExprBadType) idxuR

            bind2
                (fun arrE idxE ->
                    match arrE.SRec.ElementType with
                    | AnArrayR r -> ok (mkTypedSub r (AIdx (arrE, idxE)))
                    // TODO(CaptainHayashi): more sensible error?
                    | t -> fail (exprTypeMismatch (Fuzzy "array[]") (Exact t)))
                arrR idxR
        | ArithExp' _ -> fail (exprTypeMismatch (Fuzzy "array") (Fuzzy "integer"))
        | BoolExp' _ -> fail (exprTypeMismatch (Fuzzy "array") (Fuzzy "Boolean"))
        // We should have covered all expressions by here.
        | _ -> failwith "unreachable?[modelArrayExpr]"
    ma expr

(*
 * Views
 *)

/// Merges a list of prototype and definition parameters into one list,
/// binding the types from the former to the names from the latter.
let funcViewParMerge (ppars : TypedVar list) (dpars : Var list)
  : TypedVar list =
    List.map2 (fun ppar dpar -> withType (typeOf ppar) dpar) ppars dpars

/// Adapts Definer.lookup to the modeller's needs.
let lookupFunc (protos : FuncDefiner<ProtoInfo>) (func : Func<_>)
  : Result<DFunc, ViewError> =
    protos
    |> FuncDefiner.lookup func
    |> mapMessages (curry LookupError func.Name)
    |> bind (function
             | Some (proto, _) -> proto |> ok
             | None -> func.Name |> NoSuchView |> fail)

/// Models part of a view definition as a DFunc.
let modelDFunc
  (protos : FuncDefiner<ProtoInfo>)
  (func : Func<Var>)
  : Result<Multiset<DFunc>, ViewError> =
    func
    |> lookupFunc protos
    |> lift (fun proto ->
                 dfunc func.Name (funcViewParMerge proto.Params func.Params)
                 |> Multiset.singleton)

/// Tries to convert a view def into its model (multiset) form.
let rec modelViewSignature (protos : FuncDefiner<ProtoInfo>) =
    function
    | ViewSignature.Unit -> ok Multiset.empty
    | ViewSignature.Func dfunc ->
        let uniterated = modelDFunc protos dfunc
        lift (Multiset.map (fun f -> { Func = f; Iterator = None })) uniterated
    | ViewSignature.Join(l, r) -> trial { let! lM = modelViewSignature protos l
                                          let! rM = modelViewSignature protos r
                                          return Multiset.append lM rM }
    | ViewSignature.Iterated(dfunc, e) ->
        // Iterators have the 'int' subtype.
        let updateFunc (s : string) f = { Func = f; Iterator = Some (Int (normalRec, s)) }
        let modelledDFunc = modelDFunc protos dfunc
        lift (Multiset.map (updateFunc e)) modelledDFunc

let makeIteratorMap : TypedVar option -> VarMap =
    function
    | None              -> Map.empty
    | Some (Int (t, v)) -> Map.ofList [ v, Type.Int (t, ()) ]
    | _                 -> failwith "Iterator in iterated views must be Int type"

/// Produces the environment created by interpreting the viewdef vds using the
/// view prototype map vpm.
let rec localEnvOfViewDef (vds : DView) : Result<VarMap, ViewError> =
    let makeFuncMap { Func = {Params = ps}; Iterator = it } =
        VarMap.ofTypedVarSeq ps >>= (VarMap.combine (makeIteratorMap it))

    let funcMaps = Seq.map makeFuncMap vds
    let singleMap =
        seqBind (fun xR s -> bind (VarMap.combine s) xR) Map.empty funcMaps

    mapMessages ViewError.BadVar singleMap

/// Produces the variable environment for the constraint whose viewdef is v.
let envOfViewDef (svars : VarMap) : DView -> Result<VarMap, ViewError> =
    localEnvOfViewDef >> bind (VarMap.combine svars >> mapMessages SVarConflict)

/// Converts a single constraint to its model form.
let modelViewDef
  (svars : VarMap)
  (vprotos : FuncDefiner<ProtoInfo>)
  (av : ViewSignature, ad : Expression option)
  : Result<(DView * SVBoolExpr option), ModelError> =
    trial {
        let! vms = wrapMessages CEView (modelViewSignature vprotos) av
        let  v = vms |> Multiset.toFlatList
        let! e = envOfViewDef svars v |> mapMessages (curry CEView av)
        let! d =
            match ad with
            | Some dad ->
                dad
                |> wrapMessages CEExpr (modelBoolExpr e e id)
                |> bind (checkBoolIsNormalType >> mapMessages (fun t -> CEExpr (dad, ExprBadType t)))
                |> lift Some
            | None _ -> ok None
        return (v, d)
    }
    |> mapMessages (curry BadConstraint av)

/// <summary>
///     Checks whether a <c>DView</c> can be found in a definer.
/// </summary>
/// <param name="definer">
///     The existing definer.
/// </param>
/// <param name="dview">
///     The <c>DView</c> to check.
/// </param>
/// <returns>
///     <c>true</c> if the <c>DView</c> has been found in the definer.
///     This is a weak equality based on view names: see the remarks.
/// </returns>
/// <remarks>
///     <para>
///         We perform no sanity checking here.  It is assumed that, if the
///         view prototypes and defining views don't match, we will have
///         caught them in the main defining view modeller.
///     </para>
/// </remarks>
let inDefiner : ViewDefiner<SVBoolExpr option> -> DView -> bool =
    let namesEqual
      (vdfunc : IteratedContainer<DFunc, TypedVar option>)
      (dfunc : IteratedContainer<DFunc, TypedVar option>) =
        vdfunc.Func.Name = dfunc.Func.Name

    fun definer dview ->
        definer
        |> ViewDefiner.toSeq
        |> Seq.toList
        |> List.map fst
        |> List.exists
               (fun view ->
                    (List.length view = List.length dview)
                    && List.forall2 namesEqual view dview)

/// <summary>
///     Converts a <c>DView</c> to an indefinite <c>ViewDef</c>.
///
///     <para>
///         This instantiates the <c>DView</c> with fresh parameter
///         names, and sets its definition to <c>None</c>.
///     </para>
/// </summary>
/// <param name="dview">
///     The <c>DView</c> to convert.
/// </param>
/// <returns>
///     An indefinite constraint over <paramref name="dview" />.
/// </returns>
let searchViewToConstraint
  (dview : DView)
  : (DView * SVBoolExpr option) =
    (* To ensure likewise-named parameters in separate DFuncs don't
       clash, append fresh identifiers to all of them.

       We don't use the parameter names anyway, so this is ok.

       Do _NOT_ make dview implicit, it causes freshGen () to evaluate only
       once for the entire function (!), ruining everything. *)
    let fg = freshGen ()

    let dview' =
        List.map
            (fun { Func = { Name = name; Params = ps }; Iterator = it } ->
                 let nps =
                     List.map
                         (fun p ->
                             (withType
                                 (typeOf p)
                                    (sprintf "%s%A" (valueOf p) (getFresh fg))))
                         ps
                 { Func = { Name = name; Params = nps }; Iterator = it })
            dview

    (dview', None)

/// <summary>
///     Generates all views of the given size, from the given funcs.
/// </summary>
/// <param name="depth">
///     The size of views to generate.
/// </param>
/// <param name="funcs">
///     The pool of <c>Func</c>s to use when building views.
/// </param>
/// <returns>
///     A set of all <c>View</c>s of maximum size <paramref name="depth" />,
///     whose <c>Func</c>s are taken from <paramref name="funcs" />
/// </returns>
let genAllViewsAt depth (funcs : DFunc seq) : Set<DView> =
    let rec f depth existing =
        match depth with
        // Multiset and set conversion removes duplicate views.
        // TODO(CaptainHayashi): remove the multiset conversion somehow.
        | 0 ->
            existing
            |> Seq.map (Multiset.ofFlatList >> Multiset.toFlatList)
            |> Set.ofSeq
        | n ->
            let existing' =
                seq { yield []
                      for f in funcs do
                          for e in existing do
                              yield {Iterator = None; Func = f} :: e }
            f (depth - 1) existing'
    f depth (Seq.singleton [])

/// <summary>
///     Completes a viewdef list by generating indefinite constraints of size
///     <paramref name="depth" />.
/// </summary>
/// <param name="vprotos">
///     The map of view prototypes to use in the generated constraints.
/// </param>
/// <param name="depth">
///     The maximum view size to represent in the viewdef list.
///     A depth of 0 causes no new constraints to be generated.
/// </param>
/// <param name="viewdefs">
///     The existing viewdef list.
/// </param>
/// <returns>
///     If <paramref name="depth" /> is <c>None</c>, <paramref name="viewdefs" />.
///     Else, <paramref name="viewdefs" /> extended with indefinite
///     constraints for all views of size <paramref name="depth" />
///     generated from the views at <paramref name="vprotos" />.
/// </returns>
let addSearchDefs
  (vprotos : FuncDefiner<ProtoInfo>)
  depth
  (definer : ViewDefiner<SVBoolExpr option>)
    : ViewDefiner<SVBoolExpr option>=
    match depth with
    | None -> definer
    | Some n ->
        vprotos
        // Convert the definer back into a list of funcs.
        |> FuncDefiner.toSeq
        |> Seq.map fst
        // Then, generate the view that is the *-conjunction of all of the
        // view protos.
        |> genAllViewsAt n
        // Then, throw out any views that already exist in viewdefs...
        |> Set.filter (inDefiner definer >> not)
        // Finally, convert the view to a constraint.
        |> Set.toList
        |> Seq.map searchViewToConstraint
        // And add the result to the original definer.
        |> Seq.append (ViewDefiner.toSeq definer)
        |> ViewDefiner.ofSeq

/// Extracts the view definitions from a CollatedScript, turning each into a
/// ViewDef.
let modelViewDefs
  svars
  (vprotos : FuncDefiner<ProtoInfo>)
  { Search = s; Constraints = cs } =
    cs
    |> List.map (modelViewDef svars vprotos)
    |> collect
    |> lift (addSearchDefs vprotos s)

//
// View applications
//

/// Models an AFunc as a CFunc.
let modelCFunc
  ({ ViewProtos = protos; ThreadVars = tvars } : MethodContext)
  (afunc : Func<Expression>) =
    // First, make sure this AFunc actually has a prototype
    // and the correct number of parameters.
    afunc
    |> lookupFunc protos
    |> bind (fun proto ->
             // First, model the AFunc's parameters.
             afunc.Params
             |> Seq.map (fun e ->
                             e
                             |> modelExpr tvars tvars id
                             |> mapMessages (curry ViewError.BadExpr e))
             |> collect
             // Then, put them into a VFunc.
             |> lift (vfunc afunc.Name)
             // Now, we can use Definer's type checker to ensure
             // the params in the VFunc are of the types mentioned
             // in proto.
             |> bind (fun vfunc ->
                          FuncDefiner.checkParamTypes vfunc proto
                          |> mapMessages (curry LookupError vfunc.Name)))
    |> lift CFunc.Func

/// Tries to flatten a view AST into a CView.
/// Takes an environment of local variables, and the AST itself.
let rec modelCView (ctx : MethodContext) : View -> Result<CView, ViewError> =
    let mkCView cfunc = Multiset.singleton ({ Func = cfunc; Iterator = None })
    function
    | View.Func afunc ->
        modelCFunc ctx afunc |> lift mkCView
    | View.If(e, l, r) ->
        (* Booleans in the condition position must be of type 'bool',
           not a subtype. *)
        let teR =
            wrapMessages ViewError.BadExpr
                (modelBoolExpr ctx.ThreadVars ctx.ThreadVars id)
                e
        let eR =
            bind
                (checkBoolIsNormalType
                 >> mapMessages (ExprBadType >> fun r -> ViewError.BadExpr (e, r)))
                teR



        lift3 (fun em lm rm -> mkCView (CFunc.ITE(em, lm, rm)))
              eR
              (modelCView ctx l)
              (modelCView ctx r)
    | Unit -> Multiset.empty |> ok
    | Join(l, r) ->
        lift2 (Multiset.append)
              (modelCView ctx l)
              (modelCView ctx r)

//
// Axioms
//

/// <summary>
///     Models a Boolean lvalue given a potentially valid expression and
///     environment.
/// </summary>
/// <param name="env">The environment used for variables in the lvalue.</param>
/// <param name="idxEnv">The environment used for indexes in the lvalue.</param>
/// <param name="marker">A function that marks (or doesn't mark) vars.</param>
/// <param name="ex">The possible lvalue to model.</param>
/// <returns>If the subject is a valid lvalue, the result expression.</returns>
let modelBoolLValue
  (env : VarMap) (idxEnv : VarMap) (marker : Var -> 'Var) (ex : Expression)
  : Result<TypedBoolExpr<Sym<'Var>>, PrimError> =
    match ex with
    | RValue r -> fail (NeedLValue r)
    | LValue l -> wrapMessages BadExpr (modelBoolExpr env idxEnv marker) l

/// <summary>
///     Models an integer lvalue given a potentially valid expression and
///     environment.
/// </summary>
/// <param name="env">The environment used for variables in the lvalue.</param>
/// <param name="idxEnv">The environment used for indexes in the lvalue.</param>
/// <param name="marker">A function that marks (or doesn't mark) vars.</param>
/// <param name="ex">The possible lvalue to model.</param>
/// <returns>If the subject is a valid lvalue, the result expression.</returns>
let modelIntLValue
  (env : VarMap) (idxEnv : VarMap) (marker : Var -> 'Var) (ex : Expression)
  : Result<TypedIntExpr<Sym<'Var>>, PrimError> =
    match ex with
    | RValue r -> fail (NeedLValue r)
    | LValue l -> wrapMessages BadExpr (modelIntExpr env idxEnv marker) l

/// <summary>
///     Models an lvalue given a potentially valid expression and
///     environment.
/// </summary>
/// <param name="env">The environment of variables used for the lvalue.</param>
/// <param name="idxEnv">The environment used for indexes in the lvalue.</param>
/// <param name="marker">A function that marks (or doesn't mark) vars.</param>
/// <param name="ex">The possible lvalue to model.</param>
/// <returns>If the subject is a valid lvalue, the result expression.</returns>
let modelLValue
  (env : VarMap) (idxEnv : VarMap) (marker : Var -> 'Var) (ex : Expression)
  : Result<Expr<Sym<'Var>>, PrimError> =
    match ex with
    | RValue r -> fail (NeedLValue r)
    | LValue l -> wrapMessages BadExpr (modelExpr env idxEnv marker) l

/// Converts a Boolean load to a Prim.
let modelBoolLoad
  (ctx : MethodContext)
  (dest : Expression)
  (src : Expression)
  (mode : FetchMode)
  : Result<PrimCommand, PrimError> =
    (* In a Boolean load, the destination must be a THREAD Boolean lvalue;
                          the source must be a SHARED Boolean lvalue;
                          and the fetch mode must be Direct. *)
    let modelWithExprs dstE srcE =
        // Both expressions must have unifiable types.
        if primTypeRecsCompatible dstE.SRec srcE.SRec
        then
            match mode with
            | Direct -> ok (command "!BLoad" [ liftTypedSub Bool dstE ] [ liftTypedSub Bool srcE ])
            | Increment -> fail (IncBool src)
            | Decrement -> fail (DecBool src)
        else  // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
            fail
                (primTypeMismatch src
                    (Exact (typedBoolToType dstE))
                    (Exact (typedBoolToType srcE)))

    bind2 modelWithExprs
        (modelBoolLValue ctx.ThreadVars ctx.ThreadVars id dest)
        (modelBoolLValue ctx.SharedVars ctx.ThreadVars id src)

/// Converts an integer load to a Prim.
let modelIntLoad
  (ctx : MethodContext)
  (dest : Expression)
  (src : Expression)
  (mode : FetchMode)
  : Result<PrimCommand, PrimError> =
    (* In an integer load, the destination must be a THREAD integral lvalue;
                           the source must be a SHARED integral lvalue;
                           and the fetch mode is unconstrained. *)
    let modelWithExprs dstE srcE =
        match unifyPrimTypeRecs [ dstE.SRec; srcE.SRec ] with
        | Some srec ->
            // Direct loading is an intrinsic; the others aren't.
            let mkStored cmd =
                ok
                    (command cmd
                        [ typedIntToExpr dstE; typedIntToExpr srcE ]
                        [ typedIntToExpr srcE ])

            match mode with
            | Direct ->
                ok
                    (Intrinsic
                        (IAssign
                            { AssignType = Load
                              TypeRec = srec
                              LValue = stripTypeRec dstE
                              RValue = stripTypeRec srcE } ))
            | Increment -> mkStored "!ILoad++"
            | Decrement -> mkStored "!ILoad--"
        | None ->  // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
            fail
                (primTypeMismatch src
                    (Exact (typedIntToType dstE))
                    (Exact (typedIntToType srcE)))

    bind2 modelWithExprs
        (modelIntLValue ctx.ThreadVars ctx.ThreadVars id dest)
        (modelIntLValue ctx.SharedVars ctx.ThreadVars id src)

/// Converts a Boolean store to a Prim.
let modelBoolStore
  (ctx : MethodContext)
  (dest : Expression)
  (src : Expression)
  (mode : FetchMode)
  : Result<PrimCommand, PrimError> =
    (* In a Boolean store, the destination must a SHARED Boolean lvalue;
                           the source must be THREAD Boolean;
                           and the fetch mode must be Direct. *)
    let modelWithExprs dstE srcE =
        // Both expressions must have unifiable types.
        if primTypeRecsCompatible dstE.SRec srcE.SRec
        then
            match mode with
            | Direct -> ok (command "!BStore" [ typedBoolToExpr dstE ] [ typedBoolToExpr srcE ])
            | Increment -> fail (IncBool src)
            | Decrement -> fail (DecBool src)
        else  // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
            fail
                (primTypeMismatch src
                    (Exact (typedBoolToType dstE))
                    (Exact (typedBoolToType srcE)))

    bind2 modelWithExprs
        (modelBoolLValue ctx.SharedVars ctx.ThreadVars id dest)
        (wrapMessages BadExpr (modelBoolExpr ctx.ThreadVars ctx.ThreadVars id) src)

/// Converts an integral store to a Prim.
let modelIntStore
  (ctx : MethodContext)
  (dest : Expression)
  (src : Expression)
  (mode : FetchMode)
  : Result<PrimCommand, PrimError> =
    (* In an integral store, the destination must be SHARED and integral;
                             the source must be THREAD and integral;
                             and the fetch mode is unconstrained.  *)
    let modelWithExprs dstE srcE =
        match unifyPrimTypeRecs [ dstE.SRec; srcE.SRec ] with
        | Some srec ->
            // Direct storage is an intrinsic; the others aren't.
            let mkStored cmd =
                ok
                    (command cmd
                        [ typedIntToExpr dstE; typedIntToExpr srcE ]
                        [ typedIntToExpr srcE ])

            match mode with
            | Direct ->
                ok
                    (Intrinsic
                        (IAssign
                            { AssignType = Store
                              TypeRec = srec
                              LValue = stripTypeRec dstE
                              RValue = stripTypeRec srcE } ))
            | Increment -> mkStored "!IStore++"
            | Decrement -> mkStored "!IStore--"
        | None ->  // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
            fail
                (primTypeMismatch src
                    (Exact (typedIntToType dstE))
                    (Exact (typedIntToType srcE)))

    bind2 modelWithExprs
        (modelIntLValue ctx.SharedVars ctx.ThreadVars id dest)
        (wrapMessages BadExpr (modelIntExpr ctx.ThreadVars ctx.ThreadVars id) src)

/// <summary>
///     Models an Int and checks that it is type-compatible with another type.
/// </summary>
let modelIntWithType
  (rtype : Type)
  (env : VarMap)
  (idxEnv : VarMap)
  (expr : Expression)
  : Result<TypedIntExpr<Sym<Var>>, PrimError> =
    // TODO(CaptainHayashi): proper doc comment.
    let eR = wrapMessages BadExpr (modelIntExpr env idxEnv id) expr

    let checkType e =
        let etype = typedIntToType e
        if typesCompatible rtype etype
        then ok e
        else fail (primTypeMismatch expr (Exact rtype) (Exact etype))
    bind checkType eR

/// <summary>
///     Models a Bool and checks that it is type-compatible with another type.
/// </summary>
let modelBoolWithType
  (rtype : Type)
  (env : VarMap)
  (idxEnv : VarMap)
  (expr : Expression)
  : Result<TypedBoolExpr<Sym<Var>>, PrimError> =
    // TODO(CaptainHayashi): proper doc comment.
    let eR = wrapMessages BadExpr (modelBoolExpr env idxEnv id) expr

    let checkType e =
        let etype = typedBoolToType e
        if typesCompatible rtype etype
        then ok e
        else fail (primTypeMismatch expr (Exact rtype) (Exact etype))
    bind checkType eR

/// Converts a CAS to part-commands.
let modelCAS
  (ctx : MethodContext)
  (dest : Expression)
  (test : Expression)
  (set : Expression)
  : Result<PrimCommand, PrimError> =
    (* In a CAS, the destination must be a SHARED lvalue;
                 the test variable must be a THREAD lvalue;
                 and the to-set value must be a valid expression.

       dest, test, and set must agree on type.
       The type of dest and test influences how we interpret set. *)
    let modelWithDestAndTest destLV testLV =
        (* Determine from destPreLV and testPreLV what the type of the CAS is.
           Assume that the post-states are of the same type. *)
        match destLV, testLV with
        | Bool (dr, dlB), Bool (tr, tlB)
            when primTypeRecsCompatible dr tr ->
            // set has to be type-compatible with destLV, of course.
            let setR =
                modelBoolWithType (typeOf destLV) ctx.ThreadVars ctx.ThreadVars set 
            let modelWithSet setE =
                command "BCAS"
                    [ destLV; testLV ]
                    [ destLV; testLV; typedBoolToExpr setE ]
            lift modelWithSet setR
        | Int (dr, dlI), Int (tr, tlI)
            when primTypeRecsCompatible dr tr ->
            // set has to be type-compatible with destLV, of course.
            let setR =
                modelIntWithType (typeOf destLV) ctx.ThreadVars ctx.ThreadVars set 
            let modelWithSet setE =
                command "ICAS"
                    [ destLV; testLV ]
                    [ destLV; testLV; typedIntToExpr setE ]
            lift modelWithSet setR
        | d, t ->
            (* Oops, we have a type error.
               Arbitrarily single out test as the cause of it. *)
            fail (primTypeMismatch test (Exact (typeOf d)) (Exact (typeOf t)))

    let mdl vars = modelLValue vars ctx.ThreadVars id
    bind2 modelWithDestAndTest
        (mdl ctx.SharedVars dest)
        (mdl ctx.ThreadVars test)

/// <summary>
///     Gets the underlying variable of an lvalue.
/// </summary>
/// <param name="lv">The lvalue-candidate whose type is needed.</param>
/// <returns>
///     The lvalue's variable; will crash if the expression is not an lvalue.
/// </returns>
let rec varOfLValue (lv : Expression) : Var =
    match lv.Node with
    | Identifier i -> i
    | ArraySubscript (arr, _) -> varOfLValue arr
    | _ -> failwith "called varOfLValue with non-lvalue"

/// <summary>
///     Tries to get the type of an lvalue.
/// </summary>
/// <param name="env">The map in which the lvalue's variable exists.</param>
/// <param name="lv">The lvalue-candidate whose type is needed.</param>
/// <returns>
///     If the lvalue has a valid type, the type of that lvalue; otherwise,
///     None.
/// </returns>
let typeOfLValue (env : VarMap) (lv : Expression) : Type option =
    (* We can get the type by traversing the lvalue up to its underlying variable,
       chaining together a sequence of 'matcher functions' that respond to the
       various transformations (subscripts etc.) to that variable by peeling off
       bits of the variable's own type. *)

    (* For example, if we go through a [] to get to a variable, we need to remove
       an Array type. *)
    let matchArray var =
        match var with
        | Array ({ ElementType = eltype }, _) -> Some eltype
        | _ -> None

    // This is the part that actually traverses the expression.
    let rec walkLValue lv matcher =
        match lv.Node with
        | Identifier v ->
            (* We've found a variable x.  Its type is available in env.
               However, if we walked through some []s to get here, we need to
               apply the matcher sequence to extract the eventual element type. *)
            Option.bind (typeOf >> matcher) (VarMap.tryLookup env v)
        | ArraySubscript (arr, _) ->
            (* If we find x[i], get the type t(x) and then make a note to extract
               t(x)'s element type.  So, if arr is of type int[], we will get int. *)
            walkLValue arr (matcher >> Option.bind matchArray)
        | _ -> None
    walkLValue lv Some

/// Converts an atomic fetch to a model command.
let modelFetch
  (ctx : MethodContext)
  (dest : Expression)
  (test : Expression)
  (mode : FetchMode)
  : Result<PrimCommand, PrimError> =
    (* First, determine whether we have a fetch from shared to thread
     * (a load), or a fetch from thread to shared (a store).
     * Also figure out whether we have a Boolean or arithmetic
     * version.
     * We figure this out by looking at dest.
     *)
    let rec findModeller d =
        match d with
        | LValue _ ->
            match (typeOfLValue ctx.SharedVars d) with
            | Some (Typed.Int _) -> ok modelIntStore
            | Some (Typed.Bool _) -> ok modelBoolStore
            | Some (Typed.Array (_))
                -> fail (PrimNotImplemented "array fetch")
            | None ->
                match (typeOfLValue ctx.ThreadVars d) with
                | Some (Typed.Int _) -> ok modelIntLoad
                | Some (Typed.Bool _) -> ok modelBoolLoad
                | Some (Typed.Array (_))
                    -> fail (PrimNotImplemented "array fetch")
                | None ->
                    let v = varOfLValue d
                    fail (BadExpr (dest, Var (v, NotFound v)))
        | RValue _ -> fail (NeedLValue d)

    bind (fun f -> f ctx dest test mode) (findModeller dest)

/// <summary>
///     Models a postfix expression as a primitive.
/// </summary>
/// <param name="ctx">The context of the modeller at this position.</param>
/// <param name="operand">The postfixed expression.</param>
/// <param name="mode">The mode representing the postfix operator.</param>
/// <returns>If successful, the modelled expression.</returns>
let modelPostfix (ctx : MethodContext) (operand : Expression) (mode : FetchMode)
  : Result<PrimCommand, PrimError> =
    (* A Postfix is basically a Fetch with no destination, at this point.
       Thus, the source must be a SHARED LVALUE.
       We don't allow the Direct fetch mode, as it is useless. *)
    let modelWithOperand opE =
        match mode, opE with
        | Direct, _ -> fail Useless
        | Increment, Typed.Bool _ -> fail (IncBool operand)
        | Decrement, Typed.Bool _ -> fail (DecBool operand)
        | Increment, Typed.Int _ -> ok (command "!I++" [ opE ] [ opE ])
        | Decrement, Typed.Int _ -> ok (command "!I--" [ opE ] [ opE ])
        | _, Typed.Array (_) -> fail (PrimNotImplemented "array postfix")
    bind modelWithOperand
        (modelLValue ctx.SharedVars ctx.ThreadVars id operand)

/// Converts a single atomic command from AST to part-commands.
let rec modelAtomic : MethodContext -> Atomic -> Result<PrimCommand, PrimError> =
    fun ctx a ->
    let prim =
        match a.Node with
        | CompareAndSwap(dest, test, set) -> modelCAS ctx dest test set
        | Fetch(dest, src, mode) -> modelFetch ctx dest src mode
        | Postfix(operand, mode) -> modelPostfix ctx operand mode
        | Id -> ok (command "Id" [] [])
        | Assume e ->
            e
            |> wrapMessages BadExpr (modelBoolExpr ctx.ThreadVars ctx.ThreadVars id)
            |> lift (typedBoolToExpr >> List.singleton >> command "Assume" [])
        | Havoc var ->
            let allVarsR =
                mapMessages SymVarError (VarMap.combine ctx.ThreadVars ctx.SharedVars)
            let varMR =
                bind
                    (fun allVars ->
                        mapMessages SymVarError
                            (VarMap.lookup allVars var))
                    allVarsR
            lift (fun varM -> Intrinsic (IntrinsicCommand.Havoc varM)) varMR


        | SymAtomic sym ->
            // TODO(CaptainHayashi): split out.
            let allVarsR =
                mapMessages SymVarError (VarMap.combine ctx.ThreadVars ctx.SharedVars)
            let symArgsMR =
                bind
                    (fun allVars ->
                        (collect
                            (List.map
                                (wrapMessages BadExpr
                                    (modelExpr allVars ctx.ThreadVars id))
                                sym.Args)))
                    allVarsR
            lift
                (fun symArgsM ->
                    SymC
                        { Sentence = sym.Sentence
                          Args = symArgsM })
                symArgsMR

    lift
        (function
         | Stored cmd -> Stored { cmd with Node = Some a }
         | x -> x)
        prim

/// Converts a local variable assignment to a Prim.
and modelAssign
  (ctx : MethodContext)
  (dest : Expression)
  (src : Expression)
  : Result<PrimCommand, PrimError> =
    (* We model assignments as !ILSet or !BLSet, depending on the
       type of dest, which _must_ be a thread lvalue.
       We thus also have to make sure that src is the correct type. *)
    let modelWithDest destM =
        match destM with
        | Int (dt, d) ->
            let srcR = modelIntExpr ctx.ThreadVars ctx.ThreadVars id src
            let modelWithSrc srcE =
                match unifyPrimTypeRecs [ dt; srcE.SRec ] with
                | Some dst ->
                    ok
                        (Intrinsic
                            (IAssign
                                { AssignType = Local
                                  TypeRec = dst
                                  LValue = d
                                  RValue = stripTypeRec srcE } ))
                | None ->
                    // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
                    fail
                        (primTypeMismatch src
                            (Exact (Int (dt, ())))
                            (Exact (typedIntToType srcE)))
            bind modelWithSrc (mapMessages (curry BadExpr src) srcR)
        | Bool (dt, d) ->
            let srcR = modelBoolExpr ctx.ThreadVars ctx.ThreadVars id src
            let modelWithSrc srcE =
                match unifyPrimTypeRecs [ dt; srcE.SRec ] with
                | Some dst ->
                    ok
                        (Intrinsic
                            (BAssign
                                { AssignType = Local
                                  TypeRec = dst
                                  LValue = d
                                  RValue = stripTypeRec srcE } ))
                | None ->
                    // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
                    fail
                        (primTypeMismatch src
                            (Exact (Bool (dt, ())))
                            (Exact (typedBoolToType srcE)))
            bind modelWithSrc (mapMessages (curry BadExpr src) srcR)
        | Array (_, _) ->
            fail (PrimNotImplemented "array local assign")

    (* The permitted type of src depends on the type of dest.
       (Maybe, if the dest is ambiguous, we should invert this?) *)
    let destResult = modelLValue ctx.ThreadVars ctx.ThreadVars id dest
    bind modelWithDest destResult

/// Creates a partially resolved axiom for an if-then-else.
and modelITE
  (ctx : MethodContext)
  (i : Expression)
  (t : FullBlock<ViewExpr<View>, FullCommand>)
  (fo : FullBlock<ViewExpr<View>, FullCommand> option)
  : Result<ModellerPartCmd, MethodError> =
    let iuR =
        wrapMessages
            BadITECondition
            (modelBoolExpr ctx.ThreadVars ctx.ThreadVars id)
            i
    // An if condition needs to be of type 'bool', not a subtype.
    let iR =
        bind
            (checkBoolIsNormalType
             >> mapMessages (fun m -> BadITECondition (i, ExprBadType m)))
            iuR

    (* We need to calculate the recursive axioms first, because we
       need the inner cpairs for each to store the ITE placeholder.  *)
    let tR = modelBlock ctx t
    let fR =
        match fo with
        | Some f -> lift Some (modelBlock ctx f)
        | None -> ok None

    lift3 (curry3 ITE) iR tR fR

/// Converts a while or do-while to a PartCmd.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelWhile
  (isDo : bool)
  (ctx : MethodContext)
  (e : Expression)
  (b : FullBlock<ViewExpr<View>, FullCommand>)
  : Result<ModellerPartCmd, MethodError> =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    let euR = 
        wrapMessages
            BadWhileCondition
            (modelBoolExpr ctx.ThreadVars ctx.ThreadVars id)
            e
    // While conditions have to be of type 'bool', not a subtype.
    let eR =
        bind
            (checkBoolIsNormalType
             >> mapMessages (fun m -> BadWhileCondition (e, ExprBadType m)))
            euR

    let bR = modelBlock ctx b

    lift2 (fun eM bM -> PartCmd.While(isDo, eM, bM)) eR bR

/// Converts a PrimSet to a PartCmd.
and modelPrim
  (ctx : MethodContext)
  ({ PreAssigns = ps; Atomics = ts; PostAssigns = qs } : PrimSet)
  : Result<ModellerPartCmd, MethodError> =

    let mAssign = uncurry (wrapMessages2 BadAssign (modelAssign ctx))
    let mAtomic = wrapMessages BadAtomic (modelAtomic ctx)

    [ Seq.map mAssign ps ; Seq.map mAtomic ts ; Seq.map mAssign qs ]
    |> Seq.concat
    |> collect
    |> lift Prim

/// Converts a command to a PartCmd.
/// The list is enclosed in a Chessie result.
and modelCommand
  (ctx : MethodContext)
  (n : FullCommand)
  : Result<ModellerPartCmd, MethodError> =
    match n.Node with
    | FPrim p -> modelPrim ctx p
    | FIf(i, t, e) -> modelITE ctx i t e
    | FWhile(e, b) -> modelWhile false ctx e b
    | FDoWhile(b, e) -> modelWhile true ctx e b
    | _ -> fail (CommandNotImplemented n)

/// Converts a view expression into a CView.
and modelViewExpr (ctx : MethodContext)
  : ViewExpr<View> -> Result<ModellerViewExpr, ViewError> =
    function
    | Mandatory v -> modelCView ctx v |> lift Mandatory
    | Advisory v -> modelCView ctx v |> lift Advisory

/// Converts a pair of view and command.
and modelViewedCommand
  (ctx : MethodContext)
  (vc : FullCommand * ViewExpr<View>)
      : Result<ModellerPartCmd * ModellerViewExpr, MethodError> =
    let command, post = vc
    lift2 mkPair
          (modelCommand ctx command)
          (post |> modelViewExpr ctx
                |> mapMessages (curry MethodError.BadView post))

/// Converts the views and commands in a block.
/// The converted block is enclosed in a Chessie result.
and modelBlock
  (ctx : MethodContext)
  (block : FullBlock<ViewExpr<View>, FullCommand>)
  : Result<ModellerBlock, MethodError> =
    lift2 (fun bPreM bContentsM -> {Pre = bPreM; Cmds = bContentsM})
          (wrapMessages MethodError.BadView (modelViewExpr ctx) block.Pre)
          (block.Cmds |> Seq.map (modelViewedCommand ctx) |> collect)

/// Converts a method's views and commands.
/// The converted method is enclosed in a Chessie result.
let modelMethod
  (ctx : MethodContext)
  (meth : string * FullBlock<ViewExpr<View>, FullCommand>)
  : Result<string * ModellerBlock, ModelError> =
    let (n, b) = meth
    let bmR = mapMessages (curry BadMethod n) (modelBlock ctx b)
    lift (mkPair n) bmR

/// Checks a view prototype to see if it contains duplicate parameters.
let checkViewProtoDuplicates (proto : DesugaredViewProto)
  : Result<DesugaredViewProto, ViewProtoError> =
    match proto with
    | NoIterator (f, _) | WithIterator f ->
        f.Params
        |> Seq.map valueOf
        |> findDuplicates
        |> Seq.toList
        |> function
           | [] -> ok proto
           | ds -> List.map (fun d -> VPEDuplicateParam(proto, d)) ds |> Bad

/// Checks view prototypes and converts them to func-table form.
let modelViewProtos (protos : #(DesugaredViewProto seq))
  : Result<FuncDefiner<ProtoInfo>, ModelError> =
    let modelViewProto proto =
        proto
        |> checkViewProtoDuplicates
        |> lift
               (function
                | NoIterator (f, isAnonymous) ->
                    (f, { IsIterated = false; IsAnonymous = isAnonymous; } )
                | WithIterator f ->
                    (f, { IsIterated = true; IsAnonymous = false; } ))

    protos
    |> Seq.map (wrapMessages BadVProto modelViewProto)
    |> collect
    |> lift FuncDefiner.ofSeq

/// <summary>
///     Converts a pair of AST type literal and name into a typed variable.
/// </summary>
/// <param name="lit">The type literal to convert.</param>
/// <param name="name">The variable name to use.</param>
/// <param name="types">The map of typedefs in operation.</param>
/// <returns>
///     If the type literal is expressible in Starling's type system, the
///     corresponding type; otherwise, an error.
/// </returns>
let convertTypedVar
  (lit : AST.Types.TypeLiteral)
  (name : string)
  (types : Map<string, TypeLiteral>)
  : Result<TypedVar, TypeError> =
    let rec convType currentTypedef =
        function
        // TODO(CaptainHayashi): make typedefs less awful
        | TInt ->
            let tr = maybe normalRec (fun t -> { PrimSubtype = Named t }) currentTypedef
            ok (Int (tr, ()))
        | TBool ->
            let tr = maybe normalRec (fun t -> { PrimSubtype = Named t }) currentTypedef
            ok (Bool (tr, ()))
        | TUser ty ->
            match types.TryFind ty with
            // TODO(CaptainHayashi): this is to prevent recursion, but is too strong
            | Some (TUser _) -> fail (ImpossibleType (lit, "Typedef cannot reference a typedef"))
            | Some (TArray _) -> fail (ImpossibleType (lit, "Typedef cannot reference array type"))
            | Some t -> convType (Some ty) t
            // TODO(CaptainHayashi): bad error
            | None -> fail (ImpossibleType (lit, "Used nonexistent typedef"))
        | TArray (len, elt) ->
            lift
                (fun eltype -> Array ({ ElementType = eltype; Length = Some len }, ()))
                (convType None elt)
        (* At some point, this may (and once did) return ImpossibleType,
           hence why it is a Result. *)
    lift (fun ty -> withType ty name) (convType None lit)

/// <summary>
///     Converts a type-variable list to a variable map.
/// </summary>
/// <param name="types">The map of typedefs in operation.</param>
/// <param name="tvs">The list to convert.</param>
/// <param name="scope">The name of the scope of the variables.</param>
/// <returns>
///     If the variables' types are expressible in Starling's type system, the
///     corresponding variable map of the variables; otherwise, an error.
/// </returns>
let modelVarMap
  (types : Map<string, TypeLiteral>)
  (tvs : (TypeLiteral * string) list)
  (scope : string)
  : Result<VarMap, ModelError> =
    let cvt (t, v) = mapMessages (curry BadVarType v) (convertTypedVar t v types)
    let varsResult = collect (List.map cvt tvs)

    bind (VarMap.ofTypedVarSeq >> mapMessages (curry BadVar scope)) varsResult

/// <summary>
///     Converts a parameter to a typed variable.
/// </summary>
/// <param name="types">The map of typedefs in operation.</param>
/// <param name="par">The parameter to convert.</param>
/// <returns>
///     If the parameter is expressible in Starling's type system, the
///     corresponding type; otherwise, an error.
/// </returns>
let convertParam
  (types : Map<string, TypeLiteral>)
  (par : AST.Types.Param) : Result<TypedVar, TypeError> =
    let { ParamType = ptype; ParamName = pname } = par
    convertTypedVar ptype pname types

/// <summary>
///     Converts view prototypes from the Starling language's type system
///     to Starling's type system.
/// </summary>
let convertViewProtos
  (types : Map<string, TypeLiteral>)
  (vps : ViewProto list)
  : Result<DesugaredViewProto list, ModelError> =
    // TODO(CaptainHayashi): proper doc comment.
    let convertViewFunc vp { Name = n; Params = ps } =
        let conv = wrapMessages (fun (p, e) -> BadVProtoParamType (vp, p, e)) (convertParam types)
        let ps'Result = ps |> List.map conv |> collect
        lift (func n) ps'Result

    let convertViewProto vp =
        match vp with
        | NoIterator (func, isAnonymous) ->
            lift (fun f -> NoIterator (f, isAnonymous)) (convertViewFunc vp func)
        | WithIterator func ->
            lift (fun f -> WithIterator f) (convertViewFunc vp func)

    collect (List.map convertViewProto vps)

/// Converts a collated script to a model.
let model
  (collated : CollatedScript)
  : Result<Model<ModellerBlock, ViewDefiner<SVBoolExpr option>>, ModelError> =
    trial {
        let types = Map.ofSeq (Seq.map (fun (x, y) -> (y, x)) collated.Typedefs)

        // Make variable maps out of the shared and thread variable definitions.
        let! svars = modelVarMap types collated.SharedVars "shared"
        let! tvars = modelVarMap types collated.ThreadVars "thread"

        let desugaredMethods, unknownProtos =
            desugar tvars collated.Methods

        let! cprotos = convertViewProtos types collated.VProtos
        let! vprotos = modelViewProtos (Seq.append cprotos unknownProtos)

        let! constraints = modelViewDefs svars vprotos collated

        let mctx =
            { ViewProtos = vprotos
              SharedVars = svars
              ThreadVars = tvars }
        let! axioms =
            desugaredMethods
            |> Map.toSeq
            |> Seq.map (modelMethod mctx)
            |> collect
            |> lift Map.ofSeq

        let pragmata = List.map (fun p -> (p.Key, p.Value)) collated.Pragmata

        return
            { Pragmata = pragmata
              SharedVars = svars
              ThreadVars = tvars
              ViewDefs = constraints
              Semantics = coreSemantics
              Axioms = axioms
              ViewProtos = vprotos
              DeferredChecks = [] }
    }
