/// <summary>
///     The main part of the converter from Starling's language AST to
///     its internal representation.
/// </summary>
module Starling.Lang.Modeller

open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core
open Starling.Core.TypeSystem
open Starling.Core.TypeSystem.Check
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.View
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Core.Sub
open Starling.Lang.AST
open Starling.Lang.Collator


/// <summary>
///     Types used only in the modeller and adjacent pipeline stages.  /// </summary>
[<AutoOpen>]
module Types =
    /// A conditional (flat or if-then-else) func.
    type CFunc =
        | ITE of SVBoolExpr * Multiset<CFunc> * Multiset<CFunc>
        | Func of SVFunc

    /// A conditional view, or multiset of CFuncs.
    type CView = Multiset<CFunc>

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
            * inFalse : Block<'view, PartCmd<'view>>

    type ModellerViewExpr = ViewExpr<CView>
    type ModellerPartCmd = PartCmd<ModellerViewExpr>
    type ModellerBlock = Block<ModellerViewExpr, ModellerPartCmd>
    type ModellerMethod = Method<ModellerViewExpr, ModellerPartCmd>

    // TODO(CaptainHayashi): more consistent constructor names
    /// Represents an error when converting an expression.
    type ExprError =
        /// A non-Boolean expression was found in a Boolean position.
        | ExprNotBoolean
        /// A non-Boolean variable was found in a Boolean position.
        | VarNotBoolean of var : LValue
        /// A non-integral expression was found in an integral position.
        | ExprNotInt
        /// A non-integral variable was found in an integral position.
        | VarNotInt of var : LValue
        /// A variable usage in the expression produced a `VarMapError`.
        | Var of var : LValue * err : VarMapError
        /// A symbolic expression appeared in an ambiguous position.
        | AmbiguousSym of sym : string

    /// Represents an error when converting a view prototype.
    type ViewProtoError =
        /// A parameter name was used more than once in the same view prototype.
        | VPEDuplicateParam of AST.Types.ViewProto * param : string

    /// Represents an error when converting a view or view def.
    type ViewError =
        /// An expression in the view generated an `ExprError`.
        | BadExpr of expr : AST.Types.Expression * err : ExprError
        /// A view was requested that does not exist.
        | NoSuchView of name : string
        /// A view lookup failed.
        | LookupError of name : string * err : Instantiate.Types.Error
        /// A view used variables in incorrect ways, eg by duplicating.
        | BadVar of err : VarMapError
        /// A viewdef conflicted with the shared variables.
        | SVarConflict of err : VarMapError

    /// Represents an error when converting a constraint.
    type ConstraintError =
        /// The view definition in the constraint generated a `ViewError`.
        | CEView of vdef : AST.Types.DView * err : ViewError
        /// The expression in the constraint generated an `ExprError`.
        | CEExpr of expr : AST.Types.Expression * err : ExprError

    /// Represents an error when converting a prim.
    type PrimError =
        /// A prim used a bad shared variable.
        | BadSVar of var : LValue * err : VarMapError
        /// A prim used a bad thread variable.
        | BadTVar of var : LValue * err : VarMapError
        /// A prim used a bad variable of ambiguous scope.
        | BadAVar of var : LValue * err : VarMapError
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
        | TypeMismatch of expected : Type * bad : LValue * got : Type
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
        | BadVProto of proto : AST.Types.ViewProto * err : ViewProtoError
        /// A constraint in the program generated a `ConstraintError`.
        | BadConstraint of constr : AST.Types.DView * err : ConstraintError
        /// A method in the program generated an `MethodError`.
        | BadMethod of methname : string * err : MethodError
        /// A variable in the program generated a `VarMapError`.
        | BadVar of scope: string * err : VarMapError


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
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.View.Pretty
    open Starling.Lang.AST.Pretty

    /// Pretty-prints a CFunc.
    let rec printCFunc =
        function
        | CFunc.ITE(i, t, e) ->
            hsep [ String "if"
                   printSVBoolExpr i
                   String "then"
                   t |> printMultiset printCFunc |> ssurround "[" "]"
                   String "else"
                   e |> printMultiset printCFunc |> ssurround "[" "]" ]
        | Func v -> printSVFunc v

    /// Pretty-prints a CView.
    let printCView = printMultiset printCFunc >> ssurround "[|" "|]"

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
                       headed "False" [printBlock pView (printPartCmd pView) inFalse]]

    /// Pretty-prints expression conversion errors.
    let printExprError =
        function
        | ExprNotBoolean ->
            "expression is not suitable for use in a Boolean position" |> String
        | VarNotBoolean lv ->
            fmt "lvalue '{0}' is not a suitable type for use in a Boolean expressio    n" [ printLValue lv ]
        | ExprNotInt ->
            "expression is not suitable for use in an integral position" |> String
        | VarNotInt lv ->
            fmt "lvalue '{0}' is not a suitable type for use in an integral expre    ssion" [ printLValue lv ]
        | Var(var, err) -> wrapped "variable" (var |> printLValue) (err |> printVarMapError)
        | AmbiguousSym sym ->
            fmt
                "symbolic var '{0}' has ambiguous type: \
                 place it inside an expression with non-symbolic components"
                [ printSymbol sym ]

    /// Pretty-prints view conversion errors.
    let printViewError =
        function
        | ViewError.BadExpr(expr, err) ->
            wrapped "expression" (printExpression expr) (printExprError err)
        | NoSuchView name -> fmt "no view prototype for '{0}'" [ String name ]
        | LookupError(name, err) -> wrapped "lookup for view" (name |> String) (err |> Instantiate.Pretty.printError)
        | ViewError.BadVar err ->
            colonSep [ "invalid variable usage" |> String
                       err |> printVarMapError ]
        | SVarConflict err ->
            colonSep [ "parameters conflict with shared variables" |> String
                       err |> printVarMapError ]

    /// Pretty-prints constraint conversion errors.
    let printConstraintError =
        function
        | CEView(vdef, err) ->
            wrapped "view definition" (printDView vdef) (printViewError err)
        | CEExpr(expr, err) ->
            wrapped "expression" (printExpression expr) (printExprError err)

    /// Pretty-prints view prototype conversion errors
    let printViewProtoError =
        function
        | VPEDuplicateParam(vp, param) ->
            fmt "view proto '{0} has duplicate param {1}" [ printViewProto vp
                                                            String param ]

    /// Pretty-prints prim errors.
    let printPrimError =
        function
        | BadSVar (var, err : VarMapError) ->
            wrapped "shared lvalue" (printLValue var)
                                    (printVarMapError err)
        | BadTVar (var, err : VarMapError) ->
            wrapped "thread-local lvalue" (printLValue var)
                                          (printVarMapError err)
        | BadAVar (var, err : VarMapError) ->
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
        | TypeMismatch (expected, bad, got) ->
            fmt "lvalue '{0}' should be of type {1}, but is {2}"
                [ printLValue bad
                  printType expected
                  printType got ]
        | Useless -> String "command has no effect"

    /// Pretty-prints method errors.
    let printMethodError =
        function
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
    let printModelError =
        function
        | BadConstraint(constr, err) ->
            wrapped "constraint" (printDView constr)
                                 (printConstraintError err)
        | BadVar(scope, err) ->
            wrapped "variables in scope" (String scope) (printVarMapError err)
        | BadMethod(methname, err) ->
            wrapped "method" (String methname) (printMethodError err)
        | BadVProto(vproto, err) ->
            wrapped "view prototype" (printViewProto vproto)
                                     (printViewProtoError err)


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
                      iEq (siVar "srcA") (mkAdd2 (siVar "srcB") (AInt 1L)) ])

      // Integer load-and-decrement
      (prim "!ILoad--"  [ Int "dest"; Int "srcA" ] [ Int "srcB" ]
           <| mkAnd [ iEq (siVar "dest") (siVar "srcB")
                      iEq (siVar "srcA") (mkSub2 (siVar "srcB") (AInt 1L)) ])

      // Integer increment
      (prim "!I++"  [ Int "srcA" ] [ Int "srcB" ]
           <| iEq (siVar "srcA") (mkAdd2 (siVar "srcB") (AInt 1L)))

      // Integer decrement
      (prim "!I--"  [ Int "srcA" ] [ Int "srcB" ]
           <| iEq (siVar "srcA") (mkSub2 (siVar "srcB") (AInt 1L)))

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
  (e : Expression) : Result<Expr<Sym<'var>>, ExprError> =
    match e.Node with
    (* First, if we have a variable, the type of expression is
       determined by the type of the variable.  If the variable is
       symbolic, then we have ambiguity. *)
        | LV v ->
            v
            |> wrapMessages Var (lookupVar env)
            |> lift
                   (Mapper.map
                        (Mapper.compose
                             (Mapper.cmake (varF >> Reg))
                             (Mapper.make AVar BVar)))
        | Symbolic (sym, exprs) ->
            fail (AmbiguousSym sym)
        (* We can use the active patterns above to figure out whether we
         * need to treat this expression as arithmetic or Boolean.
         *)
        | _ -> match e with
                | ArithExp expr -> expr |> modelIntExpr env varF |> lift Expr.Int
                | BoolExp expr -> expr |> modelBoolExpr env varF |> lift Expr.Bool
                | _ -> failwith "unreachable"

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
///     but before they are placed in <c>AVar</c>.  Use this to apply
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
            |> wrapMessages Var (lookupVar env)
            |> bind (function
                     | Typed.Bool vn -> vn |> varF |> Reg |> BVar |> ok
                     | _ -> v |> VarNotBoolean |> fail)
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
                       | _ -> failwith "unreachable")
                      (mi l)
                      (mi r)
            | BoolIn as o ->
                lift2 (match o with
                       | And -> mkAnd2
                       | Or -> mkOr2
                       | _ -> failwith "unreachable")
                      (mb l)
                      (mb r)
            | AnyIn as o ->
                lift2 (match o with
                       | Eq -> mkEq
                       | Neq -> mkNeq
                       | _ -> failwith "unreachable")
                      (me l)
                      (me r)
        | _ -> fail ExprNotBoolean
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
///     but before they are placed in <c>AVar</c>.  Use this to apply
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
        | Num i -> i |> AInt |> ok
        | LV v ->
            (* Look-up the variable to ensure it a) exists and b) is of an
             * arithmetic type.
             *)
            v
            |> wrapMessages Var (lookupVar env)
            |> bind (function
                     | Typed.Int vn -> vn |> varF |> Reg |> AVar |> ok
                     | _ -> v |> VarNotInt |> fail)
        | Symbolic (sym, args) ->
            args
            |> List.map me
            |> collect
            |> lift (func sym >> Sym >> AVar)
        | BopExpr(ArithOp as op, l, r) ->
            lift2 (match op with
                   | Mul -> mkMul2
                   | Div -> mkDiv
                   | Add -> mkAdd2
                   | Sub -> mkSub2
                   | _ -> failwith "unreachable")
                  (mi l)
                  (mi r)
        | _ -> fail ExprNotInt
    mi

(*
 * Views
 *)

/// Merges a list of prototype and definition parameters into one list,
/// binding the types from the former to the names from the latter.
let funcViewParMerge ppars dpars =
    List.map2 (fun ppar dpar -> withType (typeOf ppar) dpar) ppars dpars

/// Adapts Instantiate.lookup to the modeller's needs.
let lookupFunc protos func =
    protos
    |> Instantiate.lookup func
    |> mapMessages (curry LookupError func.Name)
    |> bind (function
             | Some (proto, ()) -> proto |> ok
             | None -> func.Name |> NoSuchView |> fail)

/// Models part of a view definition as a DFunc.
let modelDFunc
  (protos : FuncTable<unit>)
  func
  : Result<Multiset<DFunc>, ViewError> =
    func
    |> lookupFunc protos
    |> lift (fun proto ->
                 dfunc func.Name (funcViewParMerge proto.Params func.Params)
                 |> Multiset.singleton)

/// Tries to convert a view def into its model (multiset) form.
let rec modelDView (protos : FuncTable<unit>) =
    function
    | DView.Unit -> ok Multiset.empty
    | DView.Func dfunc -> modelDFunc protos dfunc
    | DView.Join(l, r) -> trial { let! lM = modelDView protos l
                                  let! rM = modelDView protos r
                                  return Multiset.append lM rM }

/// Produces the environment created by interpreting the viewdef vds using the
/// view prototype map vpm.
let rec localEnvOfViewDef vds =
    vds
    |> Seq.ofList
    |> Seq.map (fun {Params = ps} -> makeVarMap ps)
    |> seqBind (fun xR s -> bind (combineMaps s) xR) Map.empty
    |> mapMessages ViewError.BadVar

/// Produces the variable environment for the constraint whose viewdef is v.
let envOfViewDef svars =
    localEnvOfViewDef >> bind (combineMaps svars >> mapMessages SVarConflict)

/// Converts a single constraint to its model form.
let modelViewDef
  svars
  (vprotos : FuncTable<unit>)
  avd
  : Result<SVBViewDef<View.Types.DView>, ModelError> =
    let av = viewOf avd

    trial {
        let! vms = wrapMessages CEView (modelDView vprotos) av
        let  v = vms |> Multiset.toFlatList
        let! e = envOfViewDef svars v |> mapMessages (curry CEView av)
        return! (match avd with
                 | Definite (_, dae) ->
                    dae
                    |> wrapMessages CEExpr (modelBoolExpr e id)
                    |> lift (fun em -> Definite (v, em))
                 | Indefinite _ ->
                     ok (Indefinite v))
    }
    |> mapMessages (curry BadConstraint av)

/// <summary>
///     Checks whether a <c>DView</c> can be found in a list of <c>ViewDef</c>s.
/// </summary>
/// <param name="viewdefs">
///     The existing viewdef list.
/// </param>
/// <param name="dview">
///     The <c>DView</c> to check.
/// </param>
/// <returns>
///     <c>true</c> if the <c>DView</c> has been found in the <c>ViewDef</c>s.
///     This is a weak equality based on view names: see the remarks.
/// </returns>
/// <remarks>
///     <para>
///         We perform no sanity checking here.  It is assumed that, if the
///         view prototypes and defining views don't match, we will have
///         caught them in the main defining view modeller.
///     </para>
/// </remarks>
let inViewDefs : ViewDef<Func<'a> list, 'b> list -> Func<'c> list -> bool = 
    fun viewdefs dview ->
    List.exists
        (fun view ->
             if (List.length view = List.length dview)
             then
                 List.forall2
                     (fun (vdfunc: Func<'a>) (dfunc : Func<'c>) -> vdfunc.Name = dfunc.Name)
                     view
                     dview
             else false)
        <| List.map viewOf viewdefs

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
  (dview : View.Types.DView) =
    (* To ensure likewise-named parameters in separate DFuncs don't
       clash, append fresh identifiers to all of them.

       We don't use the parameter names anyway, so this is ok.

       Do _NOT_ make dview implicit, it causes freshGen () to evaluate only
       once for the entire function (!), ruining everything. *)
    let fg = freshGen ()

    dview
    |> List.map
        (fun { Name = name; Params = ps } ->

             let nps =
                 List.map (fun p ->
                               (withType
                                    (typeOf p)
                                    (sprintf "%s%A" (valueOf p) (getFresh fg))))
                          ps
             { Name = name; Params = nps })
    |> Indefinite

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
let genAllViewsAt depth (funcs : DFunc seq) : Set<View.Types.DView> =
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
                              yield f :: e }
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
  (vprotos : FuncTable<unit>)
  depth
  (viewdefs : SVBViewDef<View.Types.DView> list) =
    match depth with
    | None -> viewdefs
    | Some n ->
        vprotos
        // Convert the func-table back into a func list.
        |> Instantiate.funcsInTable
        // Then, generate the view that is the *-conjunction of all of the
        // view protos.
        |> genAllViewsAt n
        // Then, throw out any views that already exist in viewdefs...
        |> Set.filter (inViewDefs viewdefs >> not)
        // Finally, convert the view to a constraint.
        |> Set.toList
        |> List.map searchViewToConstraint
        // And add the result to the original list.
        |> List.append viewdefs

/// Extracts the view definitions from a CollatedScript, turning each into a
/// ViewDef.
let modelViewDefs
  svars
  (vprotos : FuncTable<unit>)
  { Search = s; Constraints = cs } =
    cs
    |> List.map (modelViewDef svars vprotos)
    |> collect
    |> lift (addSearchDefs vprotos s)

//
// View applications
//

/// Models an AFunc as a CFunc.
let modelCFunc protos env afunc =
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
             // Now, we can use Instantiate's type checker to ensure
             // the params in the VFunc are of the types mentioned
             // in proto.
             |> bind (fun vfunc ->
                          Instantiate.checkParamTypes vfunc proto
                          |> mapMessages (curry LookupError vfunc.Name)))
    // Finally, lift to CFunc.
    |> lift CFunc.Func

/// Tries to flatten a view AST into a CView.
/// Takes an environment of local variables, and the AST itself.
let rec modelCView protos ls =
    function
    | View.Func afunc ->
        modelCFunc protos ls afunc |> lift Multiset.singleton
    | View.If(e, l, r) ->
        lift3 (fun em lm rm -> CFunc.ITE(em, lm, rm) |> Multiset.singleton)
              (e |> modelBoolExpr ls id
                 |> mapMessages (curry ViewError.BadExpr e))
              (modelCView protos ls l)
              (modelCView protos ls r)
    | Unit -> Multiset.empty |> ok
    | Join(l, r) ->
        lift2 (Multiset.append)
              (modelCView protos ls l)
              (modelCView protos ls r)

//
// Axioms
//

let (|VarIn|_|) env (lvalue : LValue) = tryLookupVar env lvalue

/// Converts a Boolean load to a Prim.
let modelBoolLoad : VarMap -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun svars dest srcExpr mode ->
    (* In a Boolean load, the destination must be LOCAL and Boolean;
     *                    the source must be a GLOBAL Boolean lvalue;
     *                    and the fetch mode must be Direct.
     *)
    match srcExpr.Node with
    | LV srcLV ->
        trial {
            let! src = wrapMessages BadSVar (lookupVar svars) srcLV
            match src, mode with
            | Typed.Bool s, Direct ->
                return
                    command
                        "!BLoad"
                            [ Bool dest ]
                            [ s |> Before |> Reg |> BVar |> Expr.Bool ]
                              
            | Typed.Bool s, Increment -> return! fail (IncBool srcExpr)
            | Typed.Bool s, Decrement -> return! fail (DecBool srcExpr)
            | _ -> return! fail (TypeMismatch (Type.Bool (), srcLV, typeOf src))
        }
    | _ -> fail (LoadNonLV srcExpr)

/// Converts an integer load to a Prim.
let modelIntLoad : VarMap -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun svars dest srcExpr mode ->
    (* In an integer load, the destination must be LOCAL and integral;
     *                    the source must be a GLOBAL arithmetic lvalue;
     *                    and the fetch mode is unconstrained.
     *)
    match srcExpr.Node with
    | LV srcLV ->
        trial {
            let! src = wrapMessages BadSVar (lookupVar svars) srcLV
            match src, mode with
            | Typed.Int s, Direct ->
                return command "!ILoad" [ Int dest ] [ s |> Before |> Reg |> AVar |> Expr.Int ]

            | Typed.Int s, Increment ->
                return command "!ILoad++" [ Int dest; Int s ] [ s |> Before |> Reg |> AVar |> Expr.Int ]

            | Typed.Int s, Decrement ->
                return command "!ILoad--" [ Int dest; Int s ] [ s |> Before |> Reg |> AVar |> Expr.Int ]

            | _ -> return! fail (TypeMismatch (Type.Int (), srcLV, typeOf src))
        }
    | _ -> fail (LoadNonLV srcExpr)

/// Converts a Boolean store to a Prim.
let modelBoolStore : VarMap -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun locals dest src mode ->
    (* In a Boolean store, the destination must be GLOBAL and Boolean;
     *                     the source must be LOCAL and Boolean;
     *                     and the fetch mode must be Direct.
     *)
    trial {
        let! sxp = wrapMessages BadExpr (modelBoolExpr locals Before) src
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
let modelIntStore : VarMap -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun locals dest src mode ->
    (* In an integral store, the destination must be GLOBAL and integral;
     *                       the source must be LOCAL and integral;
     *                       and the fetch mode must be Direct.
     *)
    trial {
        let! sxp =
            wrapMessages BadExpr (modelIntExpr locals MarkedVar.Before) src
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
let modelCAS : VarMap -> VarMap ->  LValue -> LValue -> Expression -> Result<PrimCommand, PrimError> =
    fun svars tvars destLV testLV set ->
    (* In a CAS, the destination must be SHARED;
     *           the test variable must be THREADLOCAL;
     *           and the to-set value must be a valid expression.
     * dest, test, and set must agree on type.
     * The type of dest and test influences how we interpret set.
     *)
    wrapMessages BadSVar (lookupVar svars) destLV
    >>= (fun dest ->
             mkPair dest
             <!> wrapMessages BadTVar (lookupVar tvars) testLV)
    >>= (function
         | UnifyBool (d, t) ->
             set
             |> wrapMessages BadExpr (modelBoolExpr tvars MarkedVar.Before)
             |> lift
                    (fun s ->
                        command "BCAS"
                            [ Bool d; Bool t ]
                            [ d |> sbBefore |> Expr.Bool
                              t |> sbBefore |> Expr.Bool
                              s |> Expr.Bool ] )
         | UnifyInt (d, t) ->
            set
            |> wrapMessages BadExpr (modelIntExpr tvars MarkedVar.Before)
            |> lift
                   (fun s ->
                        command "ICAS"
                            [ Int d; Int t ]
                            [ d |> siBefore |> Expr.Int
                              t |> siBefore |> Expr.Int
                              s |> Expr.Int ] )
         | UnifyFail (d, t) ->
             // Oops, we have a type error.
             // Arbitrarily single out test as the cause of it.
             fail (TypeMismatch (typeOf d, testLV, typeOf t)))

/// Converts an atomic fetch to a model command.
let modelFetch : VarMap -> VarMap -> LValue -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
    fun svars tvars destLV srcExpr mode ->
    (* First, determine whether we have a fetch from shared to thread
     * (a load), or a fetch from thread to shared (a store).
     * Also figure out whether we have a Boolean or arithmetic
     * version.
     * We figure this out by looking at dest.
     *)
    match destLV with
    | VarIn svars (Typed.Int dest) -> modelIntStore tvars dest srcExpr mode
    | VarIn svars (Typed.Bool dest) -> modelBoolStore tvars dest srcExpr mode
    | VarIn tvars (Typed.Int dest) -> modelIntLoad svars dest srcExpr mode
    | VarIn tvars (Typed.Bool dest) -> modelBoolLoad svars dest srcExpr mode
    | lv -> fail (BadAVar(lv, NotFound (flattenLV lv)))

/// Converts a single atomic command from AST to part-commands.
let rec modelAtomic : VarMap -> VarMap -> Atomic -> Result<PrimCommand, PrimError> = 
    fun svars tvars a ->
    match a.Node with
    | CompareAndSwap(dest, test, set) -> modelCAS svars tvars dest test set
    | Fetch(dest, src, mode) -> modelFetch svars tvars dest src mode
    | Postfix(operand, mode) ->
        (* A Postfix is basically a Fetch with no destination, at this point.
         * Thus, the source must be SHARED.
         * We don't allow the Direct fetch mode, as it is useless.
         *)
        trial {
            let! stype = wrapMessages BadSVar (lookupVar svars) operand
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
                return command "!I++" [ Int op ] [op |> Before |> Reg |> AVar |> Expr.Int ]
            | Decrement, Typed.Int _ ->
                return command "!I--" [ Int op ] [op |> Before |> Reg |> AVar |> Expr.Int ]
        }
    | Id -> ok (command "Id" [] [])
    | Assume e ->
        e 
        |> wrapMessages BadExpr (modelBoolExpr tvars MarkedVar.Before)
        |> lift (Expr.Bool >> List.singleton >> command "Assume" [])

/// Converts a local variable assignment to a Prim.
and modelAssign : VarMap -> LValue -> Expression -> Result<PrimCommand, PrimError> = 
    fun tvars lLV e ->
    (* We model assignments as !ILSet or !BLSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial {
        let! l = wrapMessages BadTVar (lookupVar tvars) lLV
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
and modelITE : seq<Func<Typed<string, string>> * unit> -> VarMap -> VarMap -> Expression -> Block<ViewExpr<View>, Command<ViewExpr<View>>> -> Block<ViewExpr<View>, Command<ViewExpr<View>>> -> Result<PartCmd<ViewExpr<Multiset<CFunc>>>, MethodError> =
    fun protos svars tvars i t f ->
    trial { let! iM =
                wrapMessages
                    BadITECondition
                    (modelBoolExpr tvars id)
                    i
            (* We need to calculate the recursive axioms first, because we
             * need the inner cpairs for each to store the ITE placeholder.
             *)
            let! tM = modelBlock protos svars tvars t
            let! fM = modelBlock protos svars tvars f
            return ITE(iM, tM, fM) }

/// Converts a while or do-while to a PartCmd.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelWhile isDo protos gs ls e b =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    lift2 (fun eM bM -> PartCmd.While(isDo, eM, bM))
          (wrapMessages
               BadWhileCondition
               (modelBoolExpr ls id)
               e)
          (modelBlock protos gs ls b)

/// Converts a PrimSet to a PartCmd.
and modelPrim svars tvars { PreAssigns = ps
                            Atomics = ts ;
                            PostAssigns = qs } =

    let mAssign = uncurry (wrapMessages2 BadAssign (modelAssign tvars))
    let mAtomic = wrapMessages BadAtomic (modelAtomic svars tvars)

    [ Seq.map mAssign ps ; Seq.map mAtomic ts ; Seq.map mAssign qs ]
    |> Seq.concat
    |> collect
    |> lift Prim

/// Converts a command to a PartCmd.
/// The list is enclosed in a Chessie result.
and modelCommand protos svars tvars n =
    match n.Node with
    | Command'.Prim p -> modelPrim svars tvars p
    | Command'.If(i, t, e) -> modelITE protos svars tvars i t e
    | Command'.While(e, b) -> modelWhile false protos svars tvars e b
    | Command'.DoWhile(b, e) -> modelWhile true protos svars tvars e b
    | _ -> fail (CommandNotImplemented n)

/// Converts a view expression into a CView.
and modelViewExpr protos ls =
    function
    | Mandatory v -> modelCView protos ls v |> lift Mandatory
    | Advisory v -> modelCView protos ls v |> lift Advisory

/// Converts the view and command in a ViewedCommand.
and modelViewedCommand protos gs ls {Post = post; Command = command} =
    lift2 (fun postM commandM -> {Post = postM; Command = commandM})
          (post |> modelViewExpr protos ls
                |> mapMessages (curry MethodError.BadView post))
          (command |> modelCommand protos gs ls)

/// Converts the views and commands in a list of ViewedCommands.
and modelViewedCommands protos gs ls =
    Seq.map (modelViewedCommand protos gs ls) >> collect

/// Converts the views and commands in a block.
/// The converted block is enclosed in a Chessie result.
and modelBlock protos gs ls {Pre = bPre; Contents = bContents} =
    lift2 (fun bPreM bContentsM -> {Pre = bPreM; Contents = bContentsM})
          (bPre |> modelViewExpr protos ls
                |> mapMessages (curry MethodError.BadView bPre))
          (bContents |> modelViewedCommands protos gs ls)

/// Converts a method's views and commands.
/// The converted method is enclosed in a Chessie result.
let modelMethod protos gs ls { Signature = sg ; Body = b } =
    // TODO(CaptainHayashi): method parameters
    b
    |> modelBlock protos gs ls
    |> lift (fun c -> (sg.Name, { Signature = sg ; Body = c }))
    |> mapMessages (curry BadMethod sg.Name)

/// Converts a list of methods.
/// The resulting map is enclosed in a Chessie result.
let modelMethods protos gs ls =
    // TODO(CaptainHayashi): method parameters
    Seq.map (modelMethod protos gs ls) >> collect >> lift Map.ofSeq

/// Checks a view prototype to see if it contains duplicate parameters.
let checkViewProtoDuplicates (proto : ViewProto) =
    proto.Params
    |> Seq.map valueOf
    |> findDuplicates
    |> Seq.toList
    |> function
       | [] -> ok proto
       | ds -> List.map (fun d -> VPEDuplicateParam(proto, d)) ds |> Bad

/// Checks a view prototype and converts it to an associative pair.
let modelViewProto proto =
    proto
    |> checkViewProtoDuplicates
    |> lift (fun pro -> (pro, ()))
    |> mapMessages (curry BadVProto proto)

/// Checks view prototypes and converts them to func-table form.
let modelViewProtos protos =
    protos
    |> Seq.map modelViewProto
    |> collect
    |> lift Instantiate.makeFuncTable

/// Converts a collated script to a model.
let model
  (collated : CollatedScript)
  : Result<Model<ModellerMethod, ViewToSymBoolDefiner>, ModelError> =
    trial {
        // Make variable maps out of the global and local variable definitions.
        let! globals = makeVarMap collated.Globals
                       |> mapMessages (curry BadVar "shared")
        let! locals = makeVarMap collated.Locals
                      |> mapMessages (curry BadVar "thread-local")

        let desugaredMethods, unknownProtos =
            Starling.Lang.ViewDesugar.desugar locals collated.Methods

        let! vprotos = modelViewProtos
                           (Seq.append collated.VProtos unknownProtos)

        let! constraints = modelViewDefs globals vprotos collated
        let! axioms = modelMethods vprotos globals locals desugaredMethods
        return
            { Globals = globals
              Locals = locals
              ViewDefs = constraints
              Semantics = coreSemantics
              Axioms = axioms }
    }
