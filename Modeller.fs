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
open Starling.Core.Var.Env
open Starling.Core.Var.VarMap
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Core.Traversal
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.Desugar


/// <summary>
///     Types used only in the modeller and adjacent pipeline stages.
/// </summary>
[<AutoOpen>]
module Types =
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
          ///     The environment of visible variables.
          /// </summary>
          Env : Env
          /// <summary>
          ///     A definer containing the visible view prototypes.
          /// </summary>
          ViewProtos : FuncDefiner<ProtoInfo> }

    type ModellerViewExpr = ViewExpr<IteratedGView<Sym<Var>>>
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
        /// A binary prim contained two bad expressions.
        | BadExprPair of l : AST.Types.Expression * r : AST.Types.Expression * err : ExprError
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
        /// <summary>An atomic branch contains a bad if-then-else condition.</summary>
        | BadAtomicITECondition of expr: AST.Types.Expression * err: ExprError
        /// <summary>An atomic branch contains a bad assume.</summary>
        | BadAssume of expr: AST.Types.Expression * err: ExprError

    /// Represents an error when converting a method.
    type MethodError =
        /// The method contains a semantically invalid local action.
        | BadLocal of prim : Prim * err : PrimError
        /// The method contains a semantically invalid atomic action.
        | BadAtomic of atom : DesugaredAtomic * err : PrimError
        /// The method contains a bad if-then-else condition.
        | BadITECondition of expr: AST.Types.Expression * err: ExprError
        /// The method contains a bad while condition.
        | BadWhileCondition of expr: AST.Types.Expression * err: ExprError
        /// The method contains a bad view.
        | BadView of view : ViewExpr<DesugaredGView> * err : ViewError
        /// The method contains an command not yet implemented in Starling.
        | CommandNotImplemented of cmd : FullCommand

    /// Represents an error when converting a model.
    type ModelError =
        /// <summary>
        ///     The view definer tried to constrain a view pattern as both
        ///     indefinite and definite at the same time.
        /// </summary>
        /// <remarks>
        ///     This restriction may be lifted eventually.
        /// </remarks>
        | ConjoinDefAndIndef of pattern : ViewSignature
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
    open Starling.Lang.Desugar.Pretty

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
        | BadExpr (expr, err) ->
            wrapped "expression" (printExpression expr)
                                 (printExprError err)
        | BadExprPair (l, r, err) ->
            wrapped "expressions"
                (printExpression l <+> String "and" <+> printExpression r)
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
        | BadAtomicITECondition (expr, err) ->
            wrapped "if-then-else condition" (printExpression expr)
                                             (printExprError err)
        | BadAssume (expr, err) ->
            wrapped "assumption" (printExpression expr)
                                 (printExprError err)

    /// Pretty-prints method errors.
    let printMethodError (err : MethodError) : Doc =
        match err with
        | BadLocal (prim, err) ->
            wrapped "local action" (printPrim prim) (printPrimError err)
        | BadAtomic (atom, err) ->
            wrapped "atomic action" (printDesugaredAtomic atom) (printPrimError err)
        | BadITECondition (expr, err) ->
            wrapped "if-then-else condition" (printExpression expr)
                                             (printExprError err)
        | BadWhileCondition (expr, err) ->
            wrapped "while-loop condition" (printExpression expr)
                                           (printExprError err)
        | BadView (view, err) ->
            wrapped "view expression" (printViewExpr printDesugaredGView view)
                                      (printViewError err)
        | CommandNotImplemented cmd ->
            fmt "command {0} not yet implemented" [ printFullCommand cmd ]

    /// Pretty-prints model conversion errors.
    let printModelError (err : ModelError) : Doc =
        match err with
        | ConjoinDefAndIndef pattern ->
            errorStr "view pattern"
            <+> printViewSignature pattern
            <+> errorStr "is constrained as both definite and indefinite"
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
  (body : Microcode<TypedVar, Var, unit> list)
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
                   normalBoolVar "testA" *<- normalBoolExpr (BVar "destB") ] ) ] ) ]

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
/// <param name="env">The <see cref="Env"/> of variables in the program.</param>
/// <param name="scope">
///     The level of variable scope at which this expression occurs.
/// </param>
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in the modelled expression.  Use this
///     to apply markers on variables, etc.
/// </param>
/// <param name="e">The <see cref="Expression"/> to model.</param>
/// <typeparam name="var">
///     The type of variables in the <c>Expr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A <c>Result</c>, over <c>ExprError</c>, containing the modelled
///     <c>Expr</c> on success.  The exact type parameters of the
///     expression depend on <paramref name="varF"/>.
/// </returns>
let rec modelExpr
  (env : Env)
  (scope : Scope)
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
                (wrapMessages Var (Env.lookup env scope) v)
        | Symbolic sym ->
            fail (AmbiguousSym sym)
        (* If we have an array, then work out what the type of the array's
           elements are, then walk back from there. *)
        | ArraySubscript (arr, idx) ->
            let arrR = modelArrayExpr env scope varF arr
            // Indices always have to be of type 'int', and be in local scope.
            let idxuR = modelIntExpr env (indexScopeOf scope) varF idx
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
        | ArithExp' _ -> lift (liftTypedSub Expr.Int) (modelIntExpr env scope varF e)
        | BoolExp' _ -> lift (liftTypedSub Expr.Bool) (modelBoolExpr env scope varF e)
        | _ -> failwith "unreachable[modelExpr]"

/// <summary>
///     Given an expression with one type, try to model another expression
///     that is expected to be of the same type.
/// </summary>
/// <param name="template">The expression to use as a type template.</param>
/// <param name="env">The <see cref="Env"/> of variables in the program.</param>
/// <param name="scope">
///     The level of variable scope at which this expression occurs.
/// </param>
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in the modelled expression.  Use this
///     to apply markers on variables, etc.
/// </param>
/// <param name="e">The <see cref="Expression"/> to model.</param>
/// <typeparam name="var">
///     The type of variables in the <c>Expr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A <c>Result</c>, over <c>ExprError</c>, containing the modelled
///     <c>Expr</c> on success.  The exact type parameters of the
///     expression depend on <paramref name="varF"/>.
/// </returns>
and modelExprWithType
  (template : Expr<Sym<'var>>)
  (env : Env)
  (scope : Scope)
  (varF : Var -> 'var)
  (e : Expression)
  : Result<Expr<Sym<'var>>, ExprError> =
    match template with
    | Int _ -> lift (liftTypedSub Int) (modelIntExpr env scope varF e)
    | Bool _ -> lift (liftTypedSub Bool) (modelBoolExpr env scope varF e)
    | Array _ -> lift (liftTypedSub Array) (modelArrayExpr env scope varF e)

and modelBinaryExprPair
  (env : Env)
  (scope : Scope)
  (varF : Var -> 'var)
  (l : Expression)
  (r : Expression)
  : Result<Expr<Sym<'var>> * Expr<Sym<'var>>, ExprError> =
    let me = modelExpr env scope varF
    let met x = modelExprWithType x env scope varF

    (* Symbolics introduce ambiguity, so, if we have one, we need to try
       model the non-symbol first and use its type as a crutch. *)
    let lR, rR =
        match l.Node, r.Node with
        | Symbolic _, _ ->
            let rR = me r
            let lR = bind (fun r -> met r l) rR
            (lR, rR)
        | _, Symbolic _ ->
            let lR = me l
            let rR = bind (fun l -> met l r) lR
            (lR, rR)
        | _ -> (me l, me r)

    lift2 mkPair lR rR

/// <summary>
///     Models a Starling Boolean expression as a <c>BoolExpr</c>.
///
///     <para>
///         See <c>modelExpr</c> for more information.
///     </para>
/// </summary>
/// <param name="env">The <see cref="Env"/> of variables in the program.</param>
/// <param name="scope">
///     The level of variable scope at which this expression occurs.
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
  (env : Env)
  (scope : Scope)
  (varF : Var -> 'var)
  (expr : Expression) : Result<TypedBoolExpr<Sym<'var>>, ExprError> =
    let mi = modelIntExpr env scope varF
    let me = modelExpr env scope varF
    let ma = modelArrayExpr env scope varF

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
                (wrapMessages Var (Env.lookup env scope) v)
        | Symbolic sa ->
            (* Symbols have an indefinite subtype, and can include thread-local
               scope. *)
            lift
                (Sym >> BVar >> indefBool)
                (tryMapSym (modelExpr env (symbolicScopeOf scope) varF) sa)
        | ArraySubscript (arr, idx) ->
            let arrR = ma arr
            // Indices always have to be of type 'int', and in local scope.
            let idxuR = modelIntExpr env (indexScopeOf scope) varF idx
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
                    | Imp -> mkImplies
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
                (* If at least one of the operands is a symbol, we need to
                   try infer its type from the other operand.  Simply modelling
                   both expressions will result in an ambiguity error. *)
                let lrR = modelBinaryExprPair env scope varF l r

                // We don't know the subtype of this yet...
                lift indefBool (lift (uncurry oper) lrR)
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
/// <param name="env">The <see cref="Env"/> of variables in the program.</param>
/// <param name="scope">
///     The level of variable scope at which this expression occurs.
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
  (env : Env)
  (scope : Scope)
  (varF : Var -> 'var)
  (expr : Expression) : Result<TypedIntExpr<Sym<'var>>, ExprError> =
    let me = modelExpr env scope varF
    let ma = modelArrayExpr env scope varF

    let rec mi e =
        match e.Node with
        // Numbers have indefinite subtype.
        | Num i -> ok (indefInt (IInt i))
        | Identifier v ->
            (* Look-up the variable to ensure it a) exists and b) is of an
             * arithmetic type.
             *)
            v
            |> wrapMessages Var (Env.lookup env scope)
            |> bind (function
                     | Typed.Int (ty, vn) ->
                         ok (mkTypedSub ty (IVar (Reg (varF vn))))
                     | vr ->
                        fail
                            (VarBadType
                                (v,
                                 TypeMismatch
                                    (expected = Fuzzy "int", got = Exact (typeOf vr)))))
         | Symbolic sa ->
            // Symbols have indefinite subtype.
            lift
                (Sym >> IVar >> indefInt)
                (tryMapSym (modelExpr env (symbolicScopeOf scope) varF) sa)
        | ArraySubscript (arr, idx) ->
            let arrR = ma arr
            // Indices always have to be of type 'int' and local scope.
            let idxuR = modelIntExpr env (indexScopeOf scope) varF idx
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
/// <param name="env">The <see cref="Env"/> of variables in the program.</param>
/// <param name="scope">
///     The level of variable scope at which this expression occurs.
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
  (env : Env)
  (scope : Scope)
  (varF : Var -> 'var)
  (expr : Expression)
  : Result<TypedArrayExpr<Sym<'var>>, ExprError> =
    let mi = modelIntExpr env scope varF

    let rec ma e =
        match e.Node with
        | Identifier v ->
            (* Look-up the variable to ensure it a) exists and b) is of an
             * array type.
             *)
            v
            |> wrapMessages Var (Env.lookup env scope)
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
            // Indices always have to be of type 'int' and in local scope.
            let idxuR = modelIntExpr env Thread varF idx
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

/// Produces the environment created by interpreting the viewdef vds.
let rec varMapOfViewDef (vds : DView) : Result<VarMap, ViewError> =
    let makeFuncMap { Func = {Params = ps}; Iterator = it } =
        VarMap.ofTypedVarSeq ps >>= (VarMap.combine (makeIteratorMap it))

    let funcMaps = Seq.map makeFuncMap vds
    let singleMap =
        seqBind (fun xR s -> bind (VarMap.combine s) xR) Map.empty funcMaps

    mapMessages ViewError.BadVar singleMap

/// Converts a single constraint to its model form.
let modelViewDef
  (env : Env)
  (vprotos : FuncDefiner<ProtoInfo>)
  (av : ViewSignature, ad : Expression option)
  : Result<(DView * SVBoolExpr option), ModelError> =
    trial {
        let! vms = wrapMessages CEView (modelViewSignature vprotos) av
        let  v = vms |> Multiset.toFlatList
        let! e = mapMessages (curry CEView av) (varMapOfViewDef v)

        let scope = WithMap (e, Shared)

        let! d =
            match ad with
            | Some dad ->
                dad
                |> wrapMessages CEExpr (modelBoolExpr env scope id)
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
  (env : Env)
  (vprotos : FuncDefiner<ProtoInfo>)
  (dctx : DesugarContext)
  (collated : CollatedScript) =
    let { LocalLiftView = liftName; OkayBool = okay } = dctx
    let { Search = s; Constraints = cs } = collated

    (* Add the okay variable into the emp constraint if it exists.
       If okay exists but emp is unconstrained, make a new constraint.

       TODO(MattWindsor91): this is a hack until we implement conjunctive
                            constraints. *)
    let injectOkay okay injectedAlready c = 
        let injectedNow, rhs =
            match c with
            | (ViewSignature.Unit, None) ->
                (fail (ConjoinDefAndIndef (fst c)), None)
            | (ViewSignature.Unit, Some e) ->
                (lift (fun _ -> true) injectedAlready,
                 Some (freshNode (BopExpr (And, e, okay))))
            | (_, r) -> (injectedAlready, r)
        (injectedNow, (fst c, rhs))
    let okayDefsR =
        match okay with
        | Some oname ->
            let okay = freshNode (Identifier oname)
            let injectedR, csI = mapAccumL (injectOkay okay) (ok false) cs
            lift
                (fun injected ->
                    if injected
                    then csI
                    else (ViewSignature.Unit, Some okay) :: csI)
                injectedR
        | None -> ok cs

    let explicitDefsR =
        bind (List.map (modelViewDef env vprotos) >> collect) okayDefsR
    let withSearchDefsR = lift (addSearchDefs vprotos s) explicitDefsR

    let addLiftConstraint defs =
        // TODO(MattWindsor91): remove assumption that lift's parameter is 'x'.
        maybe
            defs
            (fun n ->
                let ldef = 
                    ( [ iterated (func n [ normalBoolVar "x" ] ) None ],
                      Some (sbVar "x") )
                
                ViewDefiner.combine defs (ViewDefiner.ofSeq [ldef]))
            liftName

    lift addLiftConstraint withSearchDefsR


//
// View applications
//

/// Models a part-desugared view func.
let modelFunc
  (ctx : MethodContext)
  (afunc : Func<Expression>)
  : Result<Func<Expr<Sym<Var>>>, ViewError> =
    // First, make sure this AFunc actually has a prototype
    // and the correct number of parameters.
    afunc
    |> lookupFunc ctx.ViewProtos
    |> bind (fun proto ->
             // First, model the AFunc's parameters.
             afunc.Params
             |> Seq.map (fun e ->
                             e
                             |> modelExpr ctx.Env Thread id
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

/// Tries to model a view AST.
/// Takes an environment of local variables, and the AST itself.
let rec modelView
  (ctx : MethodContext)
  (ast : DesugaredGView)
  : Result<IteratedGView<Sym<Var>>, ViewError> =
    let mkCView cfunc = Multiset.singleton ({ Func = cfunc; Iterator = None })
    let mkCond (e : Expression) =
        (* Booleans in the condition position must be of type 'bool',
           not a subtype. *)
        let teR =
            wrapMessages ViewError.BadExpr
                (modelBoolExpr ctx.Env Thread id)
                e

        bind
            (checkBoolIsNormalType
                >> mapMessages (ExprBadType >> fun r -> ViewError.BadExpr (e, r)))
            teR

    let modelGFunc (g, f) =
        let gR = mkCond g
        let fR = modelFunc ctx f
        lift2
            (fun gM fM -> 
                (* Each of these exists once, so put it through as having
                   iterator 1. *)
                iterated { Cond = gM; Item = fM } (IInt 1L))
                gR fR
    
    let funclist = collect (List.map modelGFunc ast)
    lift Multiset.ofFlatList funclist

//
// Axioms
//

/// <summary>
///     Models an lvalue given a potentially valid expression and
///     environment.
/// </summary>
/// <param name="env">The <see cref="Env"/> of variables in the program.</param>
/// <param name="scope">
///     The level of variable scope at which this expression occurs.
/// </param>
/// <param name="marker">A function that marks (or doesn't mark) vars.</param>
/// <param name="ex">The possible lvalue to model.</param>
/// <returns>If the subject is a valid lvalue, the result expression.</returns>
let modelLValue
  (env : Env) (scope : Scope) (marker : Var -> 'Var) (ex : Expression)
  : Result<Expr<Sym<'Var>>, PrimError> =
    match ex with
    | RValue r -> fail (NeedLValue r)
    | LValue l -> wrapMessages BadExpr (modelExpr env scope marker) l

/// <summary>
///     Models an Int and checks that it is type-compatible with another type.
/// </summary>
let modelIntWithType
  (rtype : Type)
  (env : Env)
  (scope : Scope)
  (expr : Expression)
  : Result<TypedIntExpr<Sym<Var>>, PrimError> =
    // TODO(CaptainHayashi): proper doc comment.
    let eR = wrapMessages BadExpr (modelIntExpr env scope id) expr

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
  (env : Env)
  (scope : Scope)
  (expr : Expression)
  : Result<TypedBoolExpr<Sym<Var>>, PrimError> =
    // TODO(CaptainHayashi): proper doc comment.
    let eR = wrapMessages BadExpr (modelBoolExpr env scope id) expr

    let checkType e =
        let etype = typedBoolToType e
        if typesCompatible rtype etype
        then ok e
        else fail (primTypeMismatch expr (Exact rtype) (Exact etype))
    bind checkType eR


/// <summary>
///     Modellers for primitive commands.
/// </summary>
module private Prim =
    /// <summary>
    ///     Given a source expression and its modelled, type-normalised
    ///     equivalent, generate a list of commands implementing a postfix
    ///     update.
    /// </summary>
    /// <param name="srcAST">The source expression.</param>
    /// <param name="srcExpr">
    ///     The modelled, type-normalised version of <paramref name="src"/>.
    /// </param>
    /// <param name="postfix">The postfix operator.</param>
    /// <returns>
    ///     A list of <see cref="PrimCommand"/>s representing the postfix, on
    ///     success; a <see cref="PrimError"/> otherwise.
    /// </returns>
    let genPostfix (srcAST : Expression) (srcExpr : Expr<Sym<Var>>)
      (postfix : FetchMode)
      : Result<PrimCommand list, PrimError> =
        let mkIncOrDec cmd failure =
            (* For increments/decrements to make any sense,
            the source must be an lvalue, and the type must be int. *)
            match srcAST, srcExpr with
            | LValue _, Int (srec, srcI) ->
                ok [ srcExpr *<- Int (srec, cmd srcI) ]
            | LValue _, _ -> fail (failure srcAST)
            | _ -> fail (NeedLValue srcAST)

        match postfix with
        | Direct -> ok []
        | Increment -> mkIncOrDec mkInc IncBool
        | Decrement -> mkIncOrDec mkDec DecBool


    /// <summary>
    ///     Models an assignment.
    /// </summary>
    /// <param name="env">
    ///     The environment in which the assignment is being evaluated.
    /// </param>
    /// <param name="scope">
    ///     The scope in which the assignment is being evaluated.
    /// </param>
    /// <param name="dest">The destination, which must be an lvalue.</param>
    /// <param name="src">The source expression.</param>
    /// <param name="postfix">
    ///     The postfix operator for the rvalue.
    ///     For Booleans, only <c>Direct</c> is allowed.
    /// </param>
    /// <returns>
    ///     On success, the command representing the assignment;
    ///     else, the corresponding error.
    /// </returns>
    let modelAssign
      (env : Env) (scope : Scope) (dest : Expression) (src : Expression)
      (postfix : FetchMode)
      : Result<PrimCommand list, PrimError> =
        let modelWithExprs (dstE : Expr<Sym<Var>>) (srcE : Expr<Sym<Var>>) =
            match unifyTypedPair dstE srcE with
            | Some (Array _, _) -> fail (PrimNotImplemented "array assignment")
            | Some (dstEE, srcEE) ->
                let fetchCmd = dstEE *<- srcEE
                let postfixCmdR = genPostfix src srcEE postfix
                lift (fun postfixCmd -> fetchCmd :: postfixCmd) postfixCmdR

            | _ ->  // Arbitrarily blame src.  TODO(CaptainHayashi): don't?
                fail
                    (primTypeMismatch src
                        (Exact (typeOf dstE))
                        (Exact (typeOf srcE)))

        // Assignment destinations must always be lvalues.
        match dest with
        | RValue r -> fail (NeedLValue r)
        | LValue l ->
            bind (uncurry modelWithExprs)
                 (wrapMessages2 BadExprPair (modelBinaryExprPair env scope id) dest src)

    /// <summary>
    ///     Models a compare-and-swap.
    /// </summary>
    /// <param name="env">
    ///     The environment in which the CASis being evaluated.
    /// </param>
    /// <param name="scope">
    ///     The scope in which the CASis being evaluated.
    /// </param>
    /// <param name="dest">The destination, which must be an lvalue.</param>
    /// <param name="test">The test variable, which must be an lvalue.</param>
    /// <param name="src">
    ///     The source expression, which can involve thread-local and shared
    ///     variables.
    /// </param>
    /// <returns>
    ///     On success, the command representing the CAS
    ///     else, the corresponding error.
    /// </returns>
    let modelCAS
      (env : Env) (scope : Scope) (dest : Expression) (test : Expression) (set : Expression)
      : Result<PrimCommand, PrimError> =
        (* dest, test, and set must agree on type.
           The type of dest and test influences how we interpret set. *)
        let modelWithDestAndTest destLV testLV =
            (* Determine from destPreLV and testPreLV what the type of the CAS is.
            Assume that the post-states are of the same type. *)
            match destLV, testLV with
            | Bool (dr, dlB), Bool (tr, tlB)
                when primTypeRecsCompatible dr tr ->
                // set has to be type-compatible with destLV, of course.
                let setR =
                    modelBoolWithType (typeOf destLV) env Thread set 
                let modelWithSet setE =
                    command "BCAS"
                        [ destLV; testLV ]
                        [ destLV; testLV; typedBoolToExpr setE ]
                lift modelWithSet setR
            | Int (dr, dlI), Int (tr, tlI)
                when primTypeRecsCompatible dr tr ->
                // set has to be type-compatible with destLV, of course.
                let setR =
                    modelIntWithType (typeOf destLV) env Thread set 
                let modelWithSet setE =
                    command "ICAS"
                        [ destLV; testLV ]
                        [ destLV; testLV; typedIntToExpr setE ]
                lift modelWithSet setR
            | d, t ->
                (* Oops, we have a type error.
                   Arbitrarily single out test as the cause of it. *)
                fail (primTypeMismatch test (Exact (typeOf d)) (Exact (typeOf t)))

        let mdl scope = modelLValue env scope id
        bind2 modelWithDestAndTest (mdl Shared dest) (mdl Thread test)

    /// <summary>
    ///     Models a postfix expression as a primitive.
    /// </summary>
    /// <param name="env">
    ///     The environment in which the postfix is being evaluated.
    /// </param>
    /// <param name="scope">
    ///     The scope in which the postfix is being evaluated.
    /// </param>
    /// <param name="operand">
    ///     The postfixed expression, which must be a lvalue.
    /// </param>
    /// <param name="src">
    ///     The source expression, which can involve thread-local and shared
    ///     variables.
    /// </param>
    /// <param name="mode">
    ///     The fetch mode for the rvalue.
    /// </param>
    /// <returns>
    ///     On success, the command representing the postfix;
    ///     else, the corresponding error.
    /// </returns>
    let modelPostfix
      (env : Env) (operand : Expression) (mode : FetchMode)
      : Result<PrimCommand, PrimError> =
        let modelWithOperand opE =
            match mode, opE with
            // Direct in this case is a nop, so we forbid it.
            | Direct, _ -> fail Useless
            | Increment, Typed.Bool _ -> fail (IncBool operand)
            | Decrement, Typed.Bool _ -> fail (DecBool operand)
            | Increment, Typed.Int (rc, e) -> ok (opE *<- Expr.Int (rc, mkInc e))
            | Decrement, Typed.Int (rc, e) -> ok (opE *<- Expr.Int (rc, mkDec e))
            | _, Typed.Array (_) -> fail (PrimNotImplemented "array postfix")
        bind modelWithOperand (modelLValue env Any id operand)

    /// <summary>
    ///     Models a primitive command AST as a list of primitive commands.
    /// </summary>
    /// <param name="env">
    ///     The environment in which the command is being evaluated.
    /// </param>
    /// <param name="scope">
    ///     The scope in which the command is being evaluated.
    /// </param>
    /// <param name="primAST">
    ///     The syntax tree for the primitive to model.
    /// </param>
    /// <returns>
    ///     On success, the list of commands representing the primitive;
    ///     else, the corresponding error.
    /// </returns>
    let model
      (env : Env) (scope : Scope) (primAST : Prim)
      : Result<PrimCommand list, PrimError> =
        let rec prim n =
            match n.Node with
            | CompareAndSwap(dest, test, set) ->
                lift List.singleton (modelCAS env scope dest test set)
            | Fetch(dest, src, mode) -> modelAssign env scope dest src mode
            | Postfix(operand, mode) ->
                lift List.singleton (modelPostfix env operand mode)
            | Id -> ok []
            | Assume e ->
                let eModelR = wrapMessages BadExpr (modelBoolExpr env scope id) e

                // An assumption needs to be of type 'bool', not a subtype.
                let eBoolR =
                    bind
                        (checkBoolIsNormalType
                            >> mapMessages (fun m -> BadAssume (e, ExprBadType m)))
                        eModelR

                lift (Microcode.Assume >> List.singleton) eBoolR
            | Havoc var ->
                let varMR = mapMessages SymVarError (Env.lookup env scope var)
                lift (mapCTyped Reg >> mkVarExp >> havoc >> List.singleton) varMR
            | SymCommand sym ->
                // TODO(CaptainHayashi): split out.
                let symMR =
                    (tryMapSym
                        (wrapMessages BadExpr (modelExpr env scope id)) sym)
                lift (Symbol >> List.singleton) symMR

        let addNode (p : PrimCommand) : PrimCommand =
            match p with
            | Stored cmd -> Stored { cmd with Node = Some primAST }
            | x -> x

        lift (List.map addNode) (prim primAST)

/// <summary>
///     Models an atomic command AST as a list of primitive commands.
/// </summary>
/// <param name="env">
///     The environment in which the command is being evaluated.
/// </param>
/// <param name="atomicAST">
///     The desugared syntax tree for the primitive to model.
/// </param>
/// <returns>
///     On success, the list of commands representing the atomic command;
///     else, the corresponding error.
/// </returns>
let modelAtomic (env : Env) (atomicAST : DesugaredAtomic)
    : Result<PrimCommand list, PrimError> =
    let rec ma a =
        match a with
        | DAPrim primAST ->
            // Atomic actions can access variables in _any_ scope.
            Prim.model env Any primAST
        | DACond (cond = c; trueBranch = t; falseBranch = f) ->
            let cTMR =
                wrapMessages BadExpr (modelBoolExpr env Any id) c
            // An if condition needs to be of type 'bool', not a subtype.
            let cMR =
                bind
                    (checkBoolIsNormalType
                    >> mapMessages (fun m -> BadAtomicITECondition (c, ExprBadType m)))
                        cTMR
            let tMR = lift List.concat (collect (List.map ma t))
            let fMR = lift List.concat (collect (List.map ma f))
            lift3 (fun c t f -> [ Branch (c, t, f) ]) cMR tMR fMR
    ma atomicAST

/// Creates a partially resolved axiom for an if-then-else.
let rec modelITE
  (ctx : MethodContext)
  (i : Expression)
  (t : FullBlock<ViewExpr<DesugaredGView>, FullCommand>)
  (fo : FullBlock<ViewExpr<DesugaredGView>, FullCommand> option)
  : Result<ModellerPartCmd, MethodError> =
    let iuR =
        wrapMessages
            BadITECondition
            (modelBoolExpr ctx.Env Thread id)
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
  (b : FullBlock<ViewExpr<DesugaredGView>, FullCommand>)
  : Result<ModellerPartCmd, MethodError> =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    let euR = 
        wrapMessages
            BadWhileCondition
            (modelBoolExpr ctx.Env Thread id)
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
and modelPrimSet
  (ctx : MethodContext)
  ({ PreLocals = ps; Atomics = ts; PostLocals = qs } : PrimSet<DesugaredAtomic>)
  : Result<ModellerPartCmd, MethodError> =

    let mLocal = wrapMessages BadLocal (Prim.model ctx.Env Thread)
    let mAtomic = wrapMessages BadAtomic (modelAtomic ctx.Env)

    lift3
        (fun pM tM qM ->
            Prim (List.concat (seq { yield! pM; yield! tM; yield! qM })))
        (collect (List.map mLocal ps))
        (collect (List.map mAtomic ts))
        (collect (List.map mLocal qs))

/// Converts a command to a PartCmd.
/// The list is enclosed in a Chessie result.
and modelCommand
  (ctx : MethodContext)
  (n : FullCommand)
  : Result<ModellerPartCmd, MethodError> =
    match n.Node with
    | FPrim p -> modelPrimSet ctx p
    | FIf(i, t, e) -> modelITE ctx i t e
    | FWhile(e, b) -> modelWhile false ctx e b
    | FDoWhile(b, e) -> modelWhile true ctx e b
    | _ -> fail (CommandNotImplemented n)

/// Converts a view expression into a CView.
and modelViewExpr (ctx : MethodContext)
  : ViewExpr<DesugaredGView> -> Result<ModellerViewExpr, ViewError> =
    function
    | Mandatory v -> modelView ctx v |> lift Mandatory
    | Advisory v -> modelView ctx v |> lift Advisory

/// Converts a pair of view and command.
and modelViewedCommand
  (ctx : MethodContext)
  (vc : FullCommand * ViewExpr<DesugaredGView>)
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
  (block : FullBlock<ViewExpr<DesugaredGView>, FullCommand>)
  : Result<ModellerBlock, MethodError> =
    lift2 (fun bPreM bContentsM -> {Pre = bPreM; Cmds = bContentsM})
          (wrapMessages MethodError.BadView (modelViewExpr ctx) block.Pre)
          (block.Cmds |> Seq.map (modelViewedCommand ctx) |> collect)

/// Converts a method's views and commands.
/// The converted method is enclosed in a Chessie result.
let modelMethod
  (ctx : MethodContext)
  (meth : string * FullBlock<ViewExpr<DesugaredGView>, FullCommand>)
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
  (vps : ViewProto seq)
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
            lift WithIterator (convertViewFunc vp func)

    collect (Seq.map convertViewProto vps)

/// Converts a collated script to a model.
let model
  (collated : CollatedScript)
  : Result<Model<ModellerBlock, ViewDefiner<SVBoolExpr option>>, ModelError> =
    trial {
        let desugarContext, desugaredMethods = desugar collated

        let types = Map.ofSeq (Seq.map (fun (x, y) -> (y, x)) collated.Typedefs)

        // Make variable maps out of the shared and thread variable definitions.
        let! svars = modelVarMap types desugarContext.SharedVars "shared"
        let! tvars = modelVarMap types desugarContext.ThreadVars "thread"
        let env = Env.env tvars svars

        let sprotos = Seq.append desugarContext.GeneratedProtos desugarContext.ExistingProtos
        let! cprotos = convertViewProtos types sprotos
        let! vprotos = modelViewProtos cprotos

        let! constraints = modelViewDefs env vprotos desugarContext collated

        let mctx =
            { ViewProtos = vprotos
              Env = env }
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
