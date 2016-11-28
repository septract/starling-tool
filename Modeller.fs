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
        | Prim of Command
        | While of
            isDo : bool
            * expr : SVBoolExpr
            * inner : Block<'view, PartCmd<'view>>
        | ITE of
            expr : SVBoolExpr
            * inTrue : Block<'view, PartCmd<'view>>
            * inFalse : Block<'view, PartCmd<'view>> option
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
    type ModellerBlock = Block<ModellerViewExpr, ModellerPartCmd>
    type ModellerViewedCommand = ViewedCommand<ModellerViewExpr, ModellerPartCmd>
    type ModellerMethod = Method<ModellerViewExpr, ModellerPartCmd>

    /// <summary>
    ///     An error originating from the type system.
    /// </summary>
    type TypeError =
        /// <summary>
        ///     Two items that should have been the same type were not.
        /// </summary>
        | TypeMismatch of expected : Type * got : Type
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
        | VarBadType of var : LValue * err : TypeError
        /// A variable usage in the expression produced a `VarMapError`.
        | Var of var : LValue * err : VarMapError
        /// A substitution over the variable produced a `TraversalError`.
        | BadSub of err : TraversalError<unit>
        /// A symbolic expression appeared in an ambiguous position.
        | AmbiguousSym of sym : string

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

    /// Represents an error when converting a constraint.
    type ConstraintError =
        /// The view definition in the constraint generated a `ViewError`.
        | CEView of vdef : AST.Types.ViewSignature * err : ViewError
        /// The expression in the constraint generated an `ExprError`.
        | CEExpr of expr : AST.Types.Expression * err : ExprError

    /// Represents an error when converting a prim.
    type PrimError =
        /// A prim used a bad shared variable.
        | BadSVar of var : LValue * err : VarMapError
        /// A prim used a bad thread variable.
        | BadTVar of var : LValue * err : VarMapError
        /// A prim used a bad variable of ambiguous scope.
        | BadIVar of var : LValue * err : VarMapError
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
        /// A prim had a type error in it.
        | BadType of lv : LValue * err : TypeError
        /// A prim has no effect.
        | Useless

    /// Represents an error when converting a method.
    type MethodError =
        /// The method contains a semantically invalid local assign.
        | BadAssign of dest : LValue * src : AST.Types.Expression
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
        | CommandNotImplemented of cmd : AST.Types.Command<ViewExpr<View>>

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
    let rec printPartCmd (pView : 'view -> Doc) : PartCmd<'view> -> Doc =
        function
        | PartCmd.Prim prim -> Command.Pretty.printCommand prim
        | PartCmd.While(isDo, expr, inner) ->
            cmdHeaded (hsep [ String(if isDo then "Do-while" else "While")
                              (printSVBoolExpr expr) ])
                      [printBlock pView (printPartCmd pView) inner]
        | PartCmd.ITE(expr, inTrue, inFalse) ->
            cmdHeaded (hsep [String "begin if"
                             (printSVBoolExpr expr) ])
                      [headed "True" [printBlock pView (printPartCmd pView) inTrue]
                       maybe Nop
                            (fun f ->
                                headed "False" [printBlock pView (printPartCmd pView) f])
                            inFalse ]

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
            <+> quoted (printType expected)
            <&> errorStr "got"
            <+> quoted (printType got)
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
                errorStr "type error in lvalue" <+> quoted (printLValue lv)
            cmdHeaded header [ printTypeError err ]
        | Var(var, err) -> wrapped "variable" (var |> printLValue) (err |> printVarMapError)
        | BadSub err ->
            fmt "Substitution error: {0}" [ printTraversalError (fun _ -> String "()") err ]
        | AmbiguousSym sym ->
            fmt
                "symbolic var '{0}' has ambiguous type: \
                 place it inside an expression with non-symbolic components"
                [ printSymbol sym ]

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
        | BadSVar (var, err : VarMapError) ->
            wrapped "shared lvalue" (printLValue var)
                                    (printVarMapError err)
        | BadTVar (var, err : VarMapError) ->
            wrapped "thread-local lvalue" (printLValue var)
                                          (printVarMapError err)
        | BadIVar (var, err : VarMapError) ->
            wrapped "lvalue" (printLValue var) (printVarMapError err)
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
        | BadType (lv, err) ->
            let header =
                errorStr "lvalue"
                <+> quoted (printLValue lv)
                <+> errorStr "has incorrect type"
            cmdHeaded header [ printTypeError err ]


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
            fmt "command {0} not yet implemented"
                [ printCommand (printViewExpr printView) cmd ]

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
let prim : string -> TypedVar list -> TypedVar list -> SVBoolExpr -> PrimSemantics =
    fun name results args body -> { Name = name; Results = results; Args = args; Body = body }

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
    <| [ (*
       * CAS
       *)
      (prim "ICAS" [ Int "destA"; Int "testA"; ] [ Int "destB"; Int "testB"; Int "set"; ]
           <| mkAnd [ mkImplies (iEq (siVar "destB") (siVar "testB"))
                             (mkAnd [ iEq (siVar "destA") (siVar "set")
                                      iEq (siVar "testA") (siVar "testB") ] )
                      mkImplies (mkNot (iEq (siVar "destB") (siVar "testB")))
                                (mkAnd [ iEq (siVar "destA") (siVar "destB")
                                         iEq (siVar "testA") (siVar "destB") ] ) ] )
      // Boolean CAS
      (prim "BCAS" [Bool "destA"; Bool "testA"; ] [Bool "destB"; Bool "testB"; Bool "set"; ]
           <| mkAnd [ mkImplies (bEq (sbVar "destB") (sbVar "testB"))
                                (mkAnd [ bEq (sbVar "destA") (sbVar "set")
                                         bEq (sbVar "testA") (sbVar "testB") ] )
                      mkImplies (mkNot (bEq (sbVar "destB") (sbVar "testB")))
                                (mkAnd [ bEq (sbVar "destA") (sbVar "destB")
                                         bEq (sbVar "testA") (sbVar "destB") ] ) ] )

      (*
       * Atomic load
       *)
      // Integer load
      (prim "!ILoad"  [ Int "dest" ] [ Int "src" ]
           <| iEq (siVar "dest") (siVar "src"))

      // Integer load-and-increment
      (prim "!ILoad++"  [ Int "dest"; Int "srcA" ] [ Int "srcB" ]
           <| mkAnd [ iEq (siVar "dest") (siVar "srcB")
                      iEq (siVar "srcA") (mkAdd2 (siVar "srcB") (IInt 1L)) ])

      // Integer load-and-decrement
      (prim "!ILoad--"  [ Int "dest"; Int "srcA" ] [ Int "srcB" ]
           <| mkAnd [ iEq (siVar "dest") (siVar "srcB")
                      iEq (siVar "srcA") (mkSub2 (siVar "srcB") (IInt 1L)) ])

      // Integer increment
      (prim "!I++"  [ Int "srcA" ] [ Int "srcB" ]
           <| iEq (siVar "srcA") (mkAdd2 (siVar "srcB") (IInt 1L)))

      // Integer decrement
      (prim "!I--"  [ Int "srcA" ] [ Int "srcB" ]
           <| iEq (siVar "srcA") (mkSub2 (siVar "srcB") (IInt 1L)))

      // Boolean load
      (prim "!BLoad"  [ Bool "dest" ] [ Bool "src" ]
           <| bEq (sbVar "dest") (sbVar "src"))

      (*
       * Atomic store
       *)

      // Integer store
      (prim "!IStore" [ Int "dest" ] [ Int "src" ]
           <| iEq (siVar "dest") (siVar "src"))

      // Boolean store
      (prim "!BStore" [ Bool "dest" ] [ Bool "src" ]
           <| bEq (sbVar "dest") (sbVar "src"))

      (*
       * Local set
       *)

      // Integer local set
      (prim "!ILSet" [ Int "dest" ] [ Int "src" ]
           <| iEq (siVar "dest") (siVar "src"))

      // Boolean store
      (prim "!BLSet" [ Bool "dest" ] [ Bool "src" ]
           <| bEq (sbVar "dest") (sbVar "src"))

      (*
       * Assumptions
       *)

      // Identity
      (prim "Id" [] [] BTrue)

      // Assume
      (prim "Assume" [] [Bool "expr"] <| sbVar "expr") ]

(*
 * Expression translation
 *)

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
  (varF : Var -> 'var)
  (e : Expression)
  : Result<Expr<Sym<'var>>, ExprError> =
    match e.Node with
    (* First, if we have a variable, the type of expression is
       determined by the type of the variable.  If the variable is
       symbolic, then we have ambiguity. *)
        | LV v ->
            v
            |> wrapMessages Var (VarMap.lookup env)
            |> bind (
                liftWithoutContext
                    (varF >> Reg >> ok)
                    (tliftOverCTyped >> tliftToExprDest)
                >> mapMessages BadSub)
        | Symbolic (sym, exprs) ->
            fail (AmbiguousSym sym)
        (* We can use the active patterns above to figure out whether we
         * need to treat this expression as arithmetic or Boolean.
         *)
        | _ -> match e with
                | ArithExp expr -> expr |> modelIntExpr env varF |> lift Expr.Int
                | BoolExp expr -> expr |> modelBoolExpr env varF |> lift Expr.Bool
                | _ -> failwith "unreachable[modelExpr]"

/// <summary>
///     Models a Starling integral expression as a <c>BoolExpr</c>.
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
/// <typeparam name="var">
///     The type of variables in the <c>BoolExpr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A function, taking <c>Expression</c>s previously judged as
///     Boolean.  This function will return a <c>Result</c>, over
///     <c>ExprError</c>, containing the modelled <c>BoolExpr</c> on
///     success.  The exact type parameters of the expression depend on
///     <paramref name="varF"/>.
/// </returns>
and modelBoolExpr
  (env : VarMap)
  (varF : Var -> 'var)
  : Expression -> Result<BoolExpr<Sym<'var>>, ExprError> =
    let mi = modelIntExpr env varF
    let me = modelExpr env varF

    let rec mb e =
        match e.Node with
        | True -> BTrue |> ok
        | False -> BFalse |> ok
        | LV v ->
            (* Look-up the variable to ensure it a) exists and b) is of a
             * Boolean type.
             *)
            v
            |> wrapMessages Var (VarMap.lookup env)
            |> bind (function
                     | Typed.Bool vn -> vn |> varF |> Reg |> BVar |> ok
                     | vr ->
                        fail
                            (VarBadType
                                (v,
                                 TypeMismatch
                                    (expected = Type.Bool (),
                                     got = typeOf vr))))
        | Symbolic (sym, args) ->
            args
            |> List.map me
            |> collect
            |> lift (func sym >> Sym >> BVar)
        | BopExpr(BoolOp as op, l, r) ->
            match op with
            | ArithIn as o ->
                lift2 (match o with
                       | Gt -> mkGt
                       | Ge -> mkGe
                       | Le -> mkLe
                       | Lt -> mkLt
                       | _ -> failwith "unreachable[modelBoolExpr::ArithIn]")
                      (mi l)
                      (mi r)
            | BoolIn as o ->
                lift2 (match o with
                       | And -> mkAnd2
                       | Or -> mkOr2
                       | Imp -> mkImpl
                       | _ -> failwith "unreachable[modelBoolExpr::BoolIn]")
                      (mb l)
                      (mb r)
            | AnyIn as o ->
                lift2 (match o with
                       | Eq -> mkEq
                       | Neq -> mkNeq
                       | _ -> failwith "unreachable[modelBoolExpr::AnyIn]")
                      (me l)
                      (me r)
        // TODO(CaptainHayashi): figure out what the actual type is here
        | _ ->
            fail (ExprBadType (TypeMismatch (expected = Bool (), got = Int ())))
    mb

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
/// <param name="varF">
///     A function to transform any variables after they are looked-up,
///     but before they are placed in <c>IVar</c>.  Use this to apply
///     markers on variables, etc.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>IntExpr</c>, achieved by
///     applying <paramref name="varF"/> to <c>Var</c>s.
/// </typeparam>
/// <returns>
///     A function, taking <c>Expression</c>s previously judged as
///     integral.  This function will return a <c>Result</c>, over
///     <c>ExprError</c>, containing the modelled <c>IntExpr</c> on
///     success.  The exact type parameters of the expression depend on
///     <paramref name="varF"/>.
/// </returns>
and modelIntExpr
  (env : VarMap)
  (varF : Var -> 'var)
  : Expression -> Result<IntExpr<Sym<'var>>, ExprError> =
    let me = modelExpr env varF

    let rec mi e =
        match e.Node with
        | Num i -> i |> IInt |> ok
        | LV v ->
            (* Look-up the variable to ensure it a) exists and b) is of an
             * arithmetic type.
             *)
            v
            |> wrapMessages Var (VarMap.lookup env)
            |> bind (function
                     | Typed.Int vn -> vn |> varF |> Reg |> IVar |> ok
                     | vr ->
                        fail
                            (VarBadType
                                (v,
                                 TypeMismatch
                                    (expected = Type.Int (),
                                     got = typeOf vr))))
        | Symbolic (sym, args) ->
            args
            |> List.map me
            |> collect
            |> lift (func sym >> Sym >> IVar)
        | BopExpr(ArithOp as op, l, r) ->
            lift2 (match op with
                   | Mul -> mkMul2
                   | Mod -> mkMod
                   | Div -> mkDiv
                   | Add -> mkAdd2
                   | Sub -> mkSub2
                   | _ -> failwith "unreachable[modelIntExpr]")
                  (mi l)
                  (mi r)
        // TODO(CaptainHayashi): figure out what the actual type is here
        | _ ->
            fail (ExprBadType (TypeMismatch (expected = Int (), got = Bool ())))
    mi

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
        let updateFunc (s : string) f = { Func = f; Iterator = Some (Int s) }
        let modelledDFunc = modelDFunc protos dfunc
        lift (Multiset.map (updateFunc e)) modelledDFunc

let makeIteratorMap : TypedVar option -> VarMap =
    function
    | None         -> Map.empty
    | Some (Int v) -> Map.ofList [ v, Type.Int () ]
    | _            -> failwith "Iterator in iterated views must be Int type"

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
        let! d = (match ad with
                  | Some dad ->
                      dad
                      |> wrapMessages CEExpr (modelBoolExpr e id)
                      |> lift Some
                  | None _ -> ok None)
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
  ({ ViewProtos = protos; ThreadVars = env } : MethodContext)
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
                             |> modelExpr env id
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
        lift3 (fun em lm rm -> CFunc.ITE(em, lm, rm) |> mkCView)
              (e |> modelBoolExpr ctx.ThreadVars id
                 |> mapMessages (curry ViewError.BadExpr e))
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

let (|Shared|_|) ctx (lvalue : LValue) = VarMap.tryLookup ctx.SharedVars lvalue
let (|Thread|_|) ctx (lvalue : LValue) = VarMap.tryLookup ctx.ThreadVars lvalue

/// Converts a Boolean load to a Prim.
let modelBoolLoad : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun { SharedVars = svars } dest srcExpr mode ->
    (* In a Boolean load, the destination must be LOCAL and Boolean;
     *                    the source must be a GLOBAL Boolean lvalue;
     *                    and the fetch mode must be Direct.
     *)
    match srcExpr.Node with
    | LV srcLV ->
        trial {
            let! src = wrapMessages BadSVar (VarMap.lookup svars) srcLV
            match src, mode with
            | Typed.Bool s, Direct ->
                return
                    command
                        "!BLoad"
                            [ Bool dest ]
                            [ s |> Before |> Reg |> BVar |> Expr.Bool ]

            | Typed.Bool s, Increment -> return! fail (IncBool srcExpr)
            | Typed.Bool s, Decrement -> return! fail (DecBool srcExpr)
            | _ ->
                return!
                    (fail
                        (BadType
                            (srcLV,
                             TypeMismatch (Type.Bool (), typeOf src))))
        }
    | _ -> fail (LoadNonLV srcExpr)

/// Converts an integer load to a Prim.
let modelIntLoad : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun { SharedVars = svars } dest srcExpr mode ->
    (* In an integer load, the destination must be LOCAL and integral;
     *                    the source must be a GLOBAL arithmetic lvalue;
     *                    and the fetch mode is unconstrained.
     *)
    match srcExpr.Node with
    | LV srcLV ->
        trial {
            let! src = wrapMessages BadSVar (VarMap.lookup svars) srcLV
            match src, mode with
            | Typed.Int s, Direct ->
                return command "!ILoad" [ Int dest ] [ s |> Before |> Reg |> IVar |> Expr.Int ]

            | Typed.Int s, Increment ->
                return command "!ILoad++" [ Int dest; Int s ] [ s |> Before |> Reg |> IVar |> Expr.Int ]

            | Typed.Int s, Decrement ->
                return command "!ILoad--" [ Int dest; Int s ] [ s |> Before |> Reg |> IVar |> Expr.Int ]

            | _ -> return! fail (BadType (srcLV, TypeMismatch (Type.Int (), typeOf src)))
        }
    | _ -> fail (LoadNonLV srcExpr)

/// Converts a Boolean store to a Prim.
let modelBoolStore : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun { ThreadVars = tvars } dest src mode ->
    (* In a Boolean store, the destination must be GLOBAL and Boolean;
     *                     the source must be LOCAL and Boolean;
     *                     and the fetch mode must be Direct.
     *)
    trial {
        let! sxp = wrapMessages BadExpr (modelBoolExpr tvars Before) src
        match mode with
        | Direct ->
            return
                command
                    "!BStore"
                    [ Bool dest ]
                    [ sxp |> Expr.Bool ]
        | Increment -> return! fail (IncBool src)
        | Decrement -> return! fail (DecBool src)
    }

/// Converts an integral store to a Prim.
let modelIntStore : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun { ThreadVars = tvars } dest src mode ->
    (* In an integral store, the destination must be GLOBAL and integral;
     *                       the source must be LOCAL and integral;
     *                       and the fetch mode must be Direct.
     *)
    trial {
        let! sxp =
            wrapMessages BadExpr (modelIntExpr tvars MarkedVar.Before) src
        match mode with
        | Direct ->
            return
                command
                    "!IStore"
                    [ Int dest ]
                    [ sxp |> Expr.Int ]

        | Increment -> return! fail (IncExpr src)
        | Decrement -> return! fail (DecExpr src)
    }

/// Converts a CAS to part-commands.
let modelCAS : MethodContext -> LValue -> LValue -> Expression -> Result<PrimCommand, PrimError> =
    fun { SharedVars = svars; ThreadVars = tvars } destLV testLV set ->
    (* In a CAS, the destination must be SHARED;
     *           the test variable must be THREADLOCAL;
     *           and the to-set value must be a valid expression.
     * dest, test, and set must agree on type.
     * The type of dest and test influences how we interpret set.
     *)
    wrapMessages BadSVar (VarMap.lookup svars) destLV
    >>= (fun dest ->
             let v = wrapMessages BadTVar (VarMap.lookup tvars) testLV
             lift (mkPair dest) v)
    >>= (function
         | (Bool d, Bool t) ->
             set
             |> wrapMessages BadExpr (modelBoolExpr tvars MarkedVar.Before)
             |> lift
                    (fun s ->
                        command "BCAS"
                            [ Bool d; Bool t ]
                            [ d |> sbBefore |> Expr.Bool
                              t |> sbBefore |> Expr.Bool
                              s |> Expr.Bool ] )
         | (Int d, Int t) ->
            set
            |> wrapMessages BadExpr (modelIntExpr tvars MarkedVar.Before)
            |> lift
                   (fun s ->
                        command "ICAS"
                            [ Int d; Int t ]
                            [ d |> siBefore |> Expr.Int
                              t |> siBefore |> Expr.Int
                              s |> Expr.Int ] )
         | (d, t) ->
             // Oops, we have a type error.
             // Arbitrarily single out test as the cause of it.
             fail (BadType (testLV, TypeMismatch (typeOf d, typeOf t))))

/// Converts an atomic fetch to a model command.
let modelFetch : MethodContext -> LValue -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun ctx destLV srcExpr mode ->
    (* First, determine whether we have a fetch from shared to thread
     * (a load), or a fetch from thread to shared (a store).
     * Also figure out whether we have a Boolean or arithmetic
     * version.
     * We figure this out by looking at dest.
     *)
    match destLV with
    | Shared ctx (Typed.Int dest) -> modelIntStore ctx dest srcExpr mode
    | Shared ctx (Typed.Bool dest) -> modelBoolStore ctx dest srcExpr mode
    | Thread ctx (Typed.Int dest) -> modelIntLoad ctx dest srcExpr mode
    | Thread ctx (Typed.Bool dest) -> modelBoolLoad ctx dest srcExpr mode
    | lv -> fail (BadIVar(lv, NotFound (flattenLV lv)))

/// Converts a single atomic command from AST to part-commands.
let rec modelAtomic : MethodContext -> Atomic -> Result<PrimCommand, PrimError> =
    fun ctx a ->
    let prim =
        match a.Node with
        | CompareAndSwap(dest, test, set) -> modelCAS ctx dest test set
        | Fetch(dest, src, mode) -> modelFetch ctx dest src mode
        | Postfix(operand, mode) ->
            (* A Postfix is basically a Fetch with no destination, at this point.
             * Thus, the source must be SHARED.
             * We don't allow the Direct fetch mode, as it is useless.
             *)
            trial {
                let! stype = wrapMessages BadSVar (VarMap.lookup ctx.SharedVars) operand
                // TODO(CaptainHayashi): sort out lvalues...
                let op = flattenLV operand
                match mode, stype with
                | Direct, _ ->
                    return! fail Useless
                | Increment, Typed.Bool _ ->
                    return! fail (IncBool (freshNode <| LV operand))
                | Decrement, Typed.Bool _ ->
                    return! fail (DecBool (freshNode <| LV operand))
                | Increment, Typed.Int _ ->
                    return command "!I++" [ Int op ] [op |> Before |> Reg |> IVar |> Expr.Int ]
                | Decrement, Typed.Int _ ->
                    return command "!I--" [ Int op ] [op |> Before |> Reg |> IVar |> Expr.Int ]
            }
        | Id -> ok (command "Id" [] [])
        | Assume e ->
            e
            |> wrapMessages BadExpr (modelBoolExpr ctx.ThreadVars MarkedVar.Before)
            |> lift (Expr.Bool >> List.singleton >> command "Assume" [])
    lift (fun cmd -> { cmd with Node = Some a }) prim

/// Converts a local variable assignment to a Prim.
and modelAssign : MethodContext -> LValue -> Expression -> Result<PrimCommand, PrimError> =
    fun { ThreadVars = tvars } lLV e ->
    (* We model assignments as !ILSet or !BLSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial {
        let! l = wrapMessages BadTVar (VarMap.lookup tvars) lLV
        match l with
        | Typed.Bool ls ->
            let! em =
                wrapMessages BadExpr (modelBoolExpr tvars MarkedVar.Before) e
            return
                command
                    "!BLSet"
                    [ Bool ls ]
                    [ em |> Expr.Bool ]
        | Typed.Int ls ->
            let! em =
                wrapMessages BadExpr (modelIntExpr tvars MarkedVar.Before) e
            return
                command
                    "!ILSet"
                    [ Int ls ]
                    [ em |> Expr.Int ]
    }

/// Creates a partially resolved axiom for an if-then-else.
and modelITE
  : MethodContext
    -> Expression
    -> Block<ViewExpr<View>, Command<ViewExpr<View>>>
    -> Block<ViewExpr<View>, Command<ViewExpr<View>>> option
    -> Result<ModellerPartCmd, MethodError> =
    fun ctx i t fo ->
        trial { let! iM =
                    wrapMessages
                        BadITECondition
                        (modelBoolExpr ctx.ThreadVars id)
                        i
                (* We need to calculate the recursive axioms first, because we
                 * need the inner cpairs for each to store the ITE placeholder.
                 *)
                let! tM = modelBlock ctx t
                let! fM =
                    match fo with
                    | Some f -> modelBlock ctx f |> lift Some
                    | None -> ok None
                return ITE(iM, tM, fM) }

/// Converts a while or do-while to a PartCmd.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelWhile
  (isDo : bool)
  (ctx : MethodContext)
  (e : Expression)
  (b : Block<ViewExpr<View>, Command<ViewExpr<View>>>)
  : Result<ModellerPartCmd, MethodError> =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    lift2 (fun eM bM -> PartCmd.While(isDo, eM, bM))
          (wrapMessages
               BadWhileCondition
               (modelBoolExpr ctx.ThreadVars id)
               e)
          (modelBlock ctx b)

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
  (n : Command<ViewExpr<View>>)
  : Result<ModellerPartCmd, MethodError> =
    match n.Node with
    | Command'.Prim p -> modelPrim ctx p
    | Command'.If(i, t, e) -> modelITE ctx i t e
    | Command'.While(e, b) -> modelWhile false ctx e b
    | Command'.DoWhile(b, e) -> modelWhile true ctx e b
    | _ -> fail (CommandNotImplemented n)

/// Converts a view expression into a CView.
and modelViewExpr (ctx : MethodContext)
  : ViewExpr<View> -> Result<ModellerViewExpr, ViewError> =
    function
    | Mandatory v -> modelCView ctx v |> lift Mandatory
    | Advisory v -> modelCView ctx v |> lift Advisory

/// Converts the view and command in a ViewedCommand.
and modelViewedCommand
  (ctx : MethodContext)
  ({Post = post; Command = command}
     : ViewedCommand<ViewExpr<View>, Command<ViewExpr<View>>>)
  : Result<ModellerViewedCommand, MethodError> =
    lift2 (fun postM commandM -> {Post = postM; Command = commandM})
          (post |> modelViewExpr ctx
                |> mapMessages (curry MethodError.BadView post))
          (command |> modelCommand ctx)

/// Converts the views and commands in a block.
/// The converted block is enclosed in a Chessie result.
and modelBlock
  (ctx : MethodContext)
  ({Pre = bPre; Contents = bContents} :
       Block<ViewExpr<View>, Command<ViewExpr<View>>>)
  : Result<ModellerBlock, MethodError> =
    lift2 (fun bPreM bContentsM -> {Pre = bPreM; Contents = bContentsM})
          (bPre |> modelViewExpr ctx
                |> mapMessages (curry MethodError.BadView bPre))
          (bContents |> Seq.map (modelViewedCommand ctx) |> collect)

/// Converts a method's views and commands.
/// The converted method is enclosed in a Chessie result.
let modelMethod
  (ctx : MethodContext)
  ({ Signature = sg ; Body = b }
     : Method<ViewExpr<View>, Command<ViewExpr<View>>>)
  : Result<string * ModellerMethod, ModelError> =
    // TODO(CaptainHayashi): method parameters
    b
    |> modelBlock ctx
    |> lift (fun c -> (sg.Name, { Signature = sg ; Body = c }))
    |> mapMessages (curry BadMethod sg.Name)

/// Checks a view prototype to see if it contains duplicate parameters.
let checkViewProtoDuplicates (proto : DesugaredViewProto)
  : Result<DesugaredViewProto, ViewProtoError> =
    match proto with
    | NoIterator (f, _) | WithIterator (f, _) ->
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
                | WithIterator (f, _) ->
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
/// <returns>
///     If the type literal is expressible in Starling's type system, the
///     corresponding type; otherwise, an error.
/// </returns>
let convertTypedVar (lit : AST.Types.TypeLiteral) (name : string)
  : Result<TypedVar, TypeError> =
    match lit with
    | TInt -> ok (Int name)
    | TBool -> ok (Bool name)

/// <summary>
///     Converts a type-variable list to a variable map.
/// </summary>
/// <param name="tvs">The list to convert.</param>
/// <param name="scope">The name of the scope of the variables.</param>
/// <returns>
///     If the variables' types are expressible in Starling's type system, the
///     corresponding variable map of the variables; otherwise, an error.
/// </returns>
let modelVarMap (tvs : (TypeLiteral * string) list) (scope : string)
  : Result<VarMap, ModelError> =
    let cvt (t, v) = mapMessages (curry BadVarType v) (convertTypedVar t v)
    let varsResult = collect (List.map cvt tvs)

    bind (VarMap.ofTypedVarSeq >> mapMessages (curry BadVar scope)) varsResult

/// <summary>
///     Converts a parameter to a typed variable.
/// </summary>
/// <param name="par">The parameter to convert.</param>
/// <returns>
///     If the parameter is expressible in Starling's type system, the
///     corresponding type; otherwise, an error.
/// </returns>
let convertParam (par : AST.Types.Param) : Result<TypedVar, TypeError> =
    let { ParamType = ptype; ParamName = pname } = par
    convertTypedVar ptype pname

/// <summary>
///     Converts view prototypes from the Starling language's type system
///     to Starling's type system.
/// </summary>
let convertViewProtos (vps : ViewProto list)
  : Result<DesugaredViewProto list, ModelError> =
    // TODO(CaptainHayashi): proper doc comment.
    let convertViewFunc vp { Name = n; Params = ps } =
        let conv = wrapMessages (fun (p, e) -> BadVProtoParamType (vp, p, e)) convertParam
        let ps'Result = ps |> List.map conv |> collect
        lift (func n) ps'Result

    let convertViewProto vp =
        match vp with
        | NoIterator (func, isAnonymous) ->
            lift (fun f -> NoIterator (f, isAnonymous)) (convertViewFunc vp func)
        | WithIterator (func, iterator) ->
            lift (fun f -> WithIterator (f, iterator)) (convertViewFunc vp func)

    collect (List.map convertViewProto vps)

/// Converts a collated script to a model.
let model
  (collated : CollatedScript)
  : Result<Model<ModellerMethod, ViewDefiner<SVBoolExpr option>>, ModelError> =
    trial {
        // Make variable maps out of the shared and thread variable definitions.
        let! svars = modelVarMap collated.SharedVars "shared"
        let! tvars = modelVarMap collated.ThreadVars "thread"

        let desugaredMethods, unknownProtos =
            desugar tvars collated.Methods

        let! cprotos = convertViewProtos collated.VProtos
        let! vprotos = modelViewProtos (Seq.append cprotos unknownProtos)

        let! constraints = modelViewDefs svars vprotos collated

        let mctx =
            { ViewProtos = vprotos
              SharedVars = svars
              ThreadVars = tvars }
        let! axioms =
            desugaredMethods
            |> Seq.map (modelMethod mctx)
            |> collect
            |> lift Map.ofSeq

        return
            { SharedVars = svars
              ThreadVars = tvars
              ViewDefs = constraints
              Semantics = coreSemantics
              Axioms = axioms
              ViewProtos = vprotos
              DeferredChecks = [] }
    }
