module Starling.Lang.Modeller

open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Sub
open Starling.Lang.AST
open Starling.Lang.Collator


/// <summary>
///     Types used only in the modeller and adjacent pipeline stages.
/// </summary>
[<AutoOpen>]
module Types =
    /// A conditional (flat or if-then-else) func.
    type CFunc =
        | ITE of BoolExpr * Multiset<CFunc> * Multiset<CFunc>
        | Func of VFunc

    /// A conditional view, or multiset of CFuncs.
    type CView = Multiset<CFunc>

    /// A partially resolved command.
    type PartCmd<'view> =
        | Prim of Command
        | While of
            isDo : bool
            * expr : BoolExpr
            * inner : Block<'view, PartCmd<'view>>
        | ITE of
            expr : BoolExpr
            * inTrue : Block<'view, PartCmd<'view>>
            * inFalse : Block<'view, PartCmd<'view>>

    /// Methods over PartCmd.
    type PMethod<'view> = Method<'view, PartCmd<'view>>

    // TODO(CaptainHayashi): more consistent constructor names
    /// Represents an error when converting an expression.
    type ExprError =
        /// A non-Boolean expression was found in a Boolean position.
        | ExprNotBoolean
        /// A non-Boolean variable was found in a Boolean position.
        | VarNotBoolean of var : LValue
        /// A non-arithmetic expression was found in an arithmetic position.
        | ExprNotArith
        /// A non-arithmetic variable was found in an arithmetic position.
        | VarNotArith of var : LValue
        /// A variable usage in the expression produced a `VarMapError`.
        | Var of var : LValue * err : VarMapError

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
    open Starling.Core.Var.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Lang.AST.Pretty

    /// Pretty-prints a CFunc.
    let rec printCFunc =
        function
        | CFunc.ITE(i, t, e) ->
            hsep [ String "if"
                   printBoolExpr i
                   String "then"
                   t |> printMultiset printCFunc |> ssurround "[" "]"
                   String "else"
                   e |> printMultiset printCFunc |> ssurround "[" "]" ]
        | Func v -> printVFunc v

    /// Pretty-prints a CView.
    let printCView = printMultiset printCFunc >> ssurround "[|" "|]"

    /// Pretty-prints a part-cmd at the given indent level.
    let rec printPartCmd (pView : 'view -> Command) : PartCmd<'view> -> Command =
        function
        | Prim prim -> Command.Pretty.printCommand prim
        | While(isDo, expr, inner) ->
            cmdHeaded (hsep [ String(if isDo then "Do-while" else "While")
                              (printBoolExpr expr) ])
                      [printBlock pView (printPartCmd pView) inner]
        | ITE(expr, inTrue, inFalse) ->
            cmdHeaded (hsep [String "begin if"
                             (printBoolExpr expr) ])
                      [headed "True" [printBlock pView (printPartCmd pView) inTrue]
                       headed "False" [printBlock pView (printPartCmd pView) inFalse]]

    /// Pretty-prints expression conversion errors.
    let printExprError =
        function
        | ExprNotBoolean ->
            "expression is not suitable for use in a Boolean position" |> String
        | VarNotBoolean lv ->
            fmt "lvalue '{0}' is not a suitable type for use in a Boolean expressio    n" [ printLValue lv ]
        | ExprNotArith ->
            "expression is not suitable for use in an arithmetic position" |> String
        | VarNotArith lv ->
            fmt "lvalue '{0}' is not a suitable type for use in an arithmetic expre    ssion" [ printLValue lv ]
        | Var(var, err) -> wrapped "variable" (var |> printLValue) (err |> printVarMapError)

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

/// <summary>
///   The core semantic function for the imperative language.
/// </summary>
/// <remarks>
///   <para>
///     The functions beginning with '!' have special syntax in the
///     imperative language.
///   </para>
/// </remarks>
let coreSemantics =
    // TODO(CaptainHayashi): specify this in the language (standard library?).
    // TODO(CaptainHayashi): generic functions?
    // TODO(CaptainHayashi): add shared/local/expr qualifiers to parameters?
    [ (*
       * CAS
       *)

      // Integer CAS
      (func "ICAS" [ ipar "destB"; ipar "destA"
                     ipar "testB"; ipar "testA"
                     ipar "set" ],
       mkAnd [ mkImplies (aEq (aUnmarked "destB") (aUnmarked "testB"))
                         (mkAnd [ aEq (aUnmarked "destA") (aUnmarked "set")
                                  aEq (aUnmarked "testA") (aUnmarked "testB") ] )
               mkImplies (mkNot (aEq (aUnmarked "destB") (aUnmarked "testB")))
                         (mkAnd [ aEq (aUnmarked "destA") (aUnmarked "destB")
                                  aEq (aUnmarked "testA") (aUnmarked "destB") ] ) ] )
      // Boolean CAS
      (func "BCAS" [ bpar "destB"; bpar "destA"
                     bpar "testB"; bpar "testA"
                     bpar "set" ],
       mkAnd [ mkImplies (bEq (bUnmarked "destB") (bUnmarked "testB"))
                         (mkAnd [ bEq (bUnmarked "destA") (bUnmarked "set")
                                  bEq (bUnmarked "testA") (bUnmarked "testB") ] )
               mkImplies (mkNot (bEq (bUnmarked "destB") (bUnmarked "testB")))
                         (mkAnd [ bEq (bUnmarked "destA") (bUnmarked "destB")
                                  bEq (bUnmarked "testA") (bUnmarked "destB") ] ) ] )

      (*
       * Atomic load
       *)

      // Integer load
      (func "!ILoad" [ ipar "destB"; ipar "destA"
                       ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "destA") (aUnmarked "srcB")
               aEq (aUnmarked "srcA") (aUnmarked "srcB") ] )
      // Integer load-and-increment
      (func "!ILoad++" [ ipar "destB"; ipar "destA"
                         ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "destA") (aUnmarked "srcB")
               aEq (aUnmarked "srcA") (mkAdd2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Integer load-and-decrement
      (func "!ILoad--" [ ipar "destB"; ipar "destA"
                         ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "destA") (aUnmarked "srcB")
               aEq (aUnmarked "srcA") (mkSub2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Integer increment
      (func "!I++" [ ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "srcA") (mkAdd2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Integer decrement
      (func "!I--" [ ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "srcA") (mkSub2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Boolean load
      (func "!BLoad" [ bpar "destB"; bpar "destA"
                       bpar "srcB"; bpar "srcA" ],
       mkAnd [ bEq (bUnmarked "destA") (bUnmarked "srcB")
               bEq (bUnmarked "srcA") (bUnmarked "srcB") ] )

      (*
       * Atomic store
       *)

      // Integer store
      (func "!IStore" [ ipar "destB"; ipar "destA"
                        ipar "src" ],
       aEq (aUnmarked "destA") (aUnmarked "src"))
      // Boolean store
      (func "!BStore" [ bpar "destB"; bpar "destA"
                        bpar "src" ],
       bEq (bUnmarked "destA") (bUnmarked "src"))

      (*
       * Local set
       *)

      // Integer local set
      (func "!ILSet" [ ipar "destB"; ipar "destA"
                       ipar "src" ],
       aEq (aUnmarked "destA") (aUnmarked "src"))
      // Boolean store
      (func "!BLSet" [ bpar "destB"; bpar "destA"
                       bpar "src" ],
       bEq (bUnmarked "destA") (bUnmarked "src"))

      (*
       * Assumptions
       *)

      // Identity
      (func "Id" [], BTrue)
      // Assume
      (func "Assume" [ bpar "expr" ], bUnmarked "expr") ]

(*
 * Expression translation
 *)

/// Converts a Starling expression of ambiguous type to a Z3 predicate using
/// the given environment.
let rec modelExpr env expr =
    match expr with
    (* First, if we have a variable, the type of expression is
     * determined by the type of the variable.
     *)
    | LV v ->
        (* Look-up the variable to ensure it a) exists and b) is of a
         * Boolean type.
         *)
        lookupVar env v
        |> mapMessages ((curry Var) v)
        |> lift (function
                 | Type.Bool -> v |> mkBoolLV |> BExpr
                 | Type.Int -> v |> mkIntLV |> AExpr)
    (* We can use the active patterns above to figure out whether we
     * need to treat this expression as arithmetic or Boolean.
     *)
    | ArithExp -> modelArithExpr env expr |> lift AExpr
    | BoolExp -> modelBoolExpr env expr |> lift BExpr
    | _ -> failwith "unreachable"

/// Converts a Starling Boolean expression to a Z3 predicate using
/// the given partial model and environment.
and modelBoolExpr env expr =
    match expr with
    | True -> BTrue |> ok
    | False -> BFalse |> ok
    | LV v ->
        (* Look-up the variable to ensure it a) exists and b) is of a
         * Boolean type.
         *)
        v
        |> wrapMessages Var (lookupVar env)
        |> bind (function
                 | Type.Bool -> v |> mkBoolLV |> ok
                 | _ -> v |> VarNotBoolean |> fail)
    | Bop(BoolOp as op, l, r) ->
        match op with
        | ArithIn as o ->
            lift2 (match o with
                   | Gt -> mkGt
                   | Ge -> mkGe
                   | Le -> mkLe
                   | Lt -> mkLt
                   | _ -> failwith "unreachable")
                  (modelArithExpr env l)
                  (modelArithExpr env r)
        | BoolIn as o ->
            lift2 (match o with
                   | And -> mkAnd2
                   | Or -> mkOr2
                   | _ -> failwith "unreachable")
                  (modelBoolExpr env l)
                  (modelBoolExpr env r)
        | AnyIn as o ->
            lift2 (match o with
                   | Eq -> mkEq
                   | Neq -> mkNeq
                   | _ -> failwith "unreachable")
                  (modelExpr env l)
                  (modelExpr env r)
    | _ -> fail ExprNotBoolean

/// Converts a Starling arithmetic expression ot a Z3 predicate using
/// the given Z3 context.
and modelArithExpr env expr =
    match expr with
    | Int i -> i |> AInt |> ok
    | LV v ->
        (* Look-up the variable to ensure it a) exists and b) is of an
         * arithmetic type.
         *)
        v
        |> wrapMessages Var (lookupVar env)
        |> bind (function
                 | Type.Int -> v |> mkIntLV |> ok
                 | _ -> v |> VarNotArith |> fail)
    | Bop(ArithOp as op, l, r) ->
        lift2 (match op with
               | Mul -> mkMul2
               | Div -> mkDiv
               | Add -> mkAdd2
               | Sub -> mkSub2
               | _ -> failwith "unreachable")
              (modelArithExpr env l)
              (modelArithExpr env r)
    | _ -> fail ExprNotArith

(*
 * Views
 *)

/// Merges a list of prototype and definition parameters into one list,
/// binding the types from the former to the names from the latter.
let funcViewParMerge ppars dpars = List.map2 (fun (ty, _) name -> (ty, name)) ppars dpars

/// Adapts Instantiate.lookup to the modeller's needs.
let lookupFunc protos func =
    protos
    |> Instantiate.lookup func
    |> mapMessages (curry LookupError func.Name)
    |> bind (function
             | Some (proto, ()) -> proto |> ok
             | None -> func.Name |> NoSuchView |> fail)

/// Models part of a view definition as a DFunc.
let modelDFunc protos func =
    func
    |> lookupFunc protos
    |> lift (fun proto ->
                 dfunc func.Name (funcViewParMerge proto.Params func.Params) |> Multiset.singleton)

/// Tries to convert a view def into its model (multiset) form.
let rec modelDView protos =
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
let modelViewDef svars vprotos avd =
    let av = viewOf avd

    trial {
        let vplist = List.ofSeq vprotos

        let! vms = modelDView vplist av |> mapMessages (curry CEView av) 
        let  v = vms |> Multiset.toFlatList
        let! e = envOfViewDef svars v |> mapMessages (curry CEView av)
        return! (match avd with
                 | Definite (_, dae) ->
                    modelBoolExpr e dae
                    |> mapMessages (curry CEExpr dae)
                    |> lift (fun em -> Definite (v, em))
                 | Uninterpreted (_, sym) ->
                     ok (Uninterpreted (v, sym))
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
let inViewDefs viewdefs dview =
    List.exists
        (function
         | DefOver view ->
             if (List.length view = List.length dview)
             then
                 List.forall2
                     (fun vdfunc dfunc -> vdfunc.Name = dfunc.Name)
                     view
                     dview
             else false)
        viewdefs

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
let searchViewToConstraint dview =
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
                 List.map (fun (ty, str) ->
                               (ty, sprintf "%s%A" str (getFresh fg)))
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
let genAllViewsAt depth funcs =
    let rec f depth existing =
        match depth with
        // Multiset and set conversion removes duplicate views.
        | 0 -> existing |> Seq.map (Multiset.ofFlatList >> Multiset.toFlatList) |> Set.ofSeq
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
let addSearchDefs vprotos depth viewdefs =
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
let modelViewDefs svars vprotos { Search = s; Constraints = cs } =
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
                             |> modelExpr env
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
              (e |> modelBoolExpr ls
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
let modelBoolLoad svars dest src mode =
    (* In a Boolean load, the destination must be LOCAL and Boolean;
     *                    the source must be a GLOBAL Boolean lvalue;
     *                    and the fetch mode must be Direct.
     *)
    match src with
    | LV s ->
        trial {
            let! stype = lookupVar svars s |> mapMessages (curry BadSVar s)
            match stype, mode with
            | Type.Bool, Direct ->
                return func "!BLoad" [ dest |> blBefore; dest |> blAfter
                                       s |> blBefore; s |> blAfter ]
            | Type.Bool, Increment -> return! fail (IncBool src)
            | Type.Bool, Decrement -> return! fail (DecBool src)
            | _ -> return! fail (TypeMismatch(Type.Bool, s, stype))
        }
    | _ -> fail (LoadNonLV src)

/// Converts an integer load to a Prim.
let modelIntLoad svars dest src mode =
    (* In an integer load, the destination must be LOCAL and integral;
     *                    the source must be a GLOBAL arithmetic lvalue;
     *                    and the fetch mode is unconstrained.
     *)
    match src with
    | LV s ->
        trial {
            let! stype = lookupVar svars s
                         |> mapMessages (curry BadSVar s)
            match stype, mode with
            | Type.Int, Direct ->
                return func "!ILoad" [ dest |> ilBefore; dest |> ilAfter
                                       s |> ilBefore; s |> ilAfter ]
            | Type.Int, Increment ->
                return func "!ILoad++" [ dest |> ilBefore; dest |> ilAfter
                                         s |> ilBefore; s |> ilAfter ]
            | Type.Int, Decrement ->
                return func "!ILoad--" [ dest |> ilBefore; dest |> ilAfter
                                         s |> ilBefore; s |> ilAfter ]
            | _ -> return! fail (TypeMismatch(Type.Int, s, stype))
        }
    | _ -> fail (LoadNonLV src)

/// Converts a Boolean store to a Prim.
let modelBoolStore locals dest src mode =
    (* In a Boolean store, the destination must be GLOBAL and Boolean;
     *                     the source must be LOCAL and Boolean;
     *                     and the fetch mode must be Direct.
     *)
    trial {
        let! sxp = modelBoolExpr locals src |> mapMessages (curry BadExpr src)
        match mode with
        | Direct -> return func "!BStore" [ dest |> blBefore; dest |> blAfter
                                            sxp |> BExpr |> before ]
        | Increment -> return! fail (IncBool src)
        | Decrement -> return! fail (DecBool src)
    }

/// Converts an integral store to a Prim.
let modelIntStore locals dest src mode =
    (* In an integral store, the destination must be GLOBAL and integral;
     *                       the source must be LOCAL and integral;
     *                       and the fetch mode must be Direct.
     *)
    trial {
        let! sxp = modelArithExpr locals src |> mapMessages (curry BadExpr src)
        match mode with
        | Direct -> return func "!IStore" [ dest |> ilBefore; dest |> ilAfter
                                            sxp |> AExpr |> before ]
        | Increment -> return! fail (IncExpr src)
        | Decrement -> return! fail (DecExpr src)
    }

/// Converts a CAS to part-commands.
let modelCAS svars tvars dest test set =
    (* In a CAS, the destination must be SHARED;
     *           the test variable must be THREADLOCAL;
     *           and the to-set value must be a valid expression.
     * dest, test, and set must agree on type.
     * The type of dest and test influences how we interpret set.
     *)
    trial {
        let! dtype = lookupVar svars dest
                     |> mapMessages (curry BadSVar dest)
        let! ttype = lookupVar tvars test
                     |> mapMessages (curry BadTVar dest)
        match dtype, ttype with
        | Type.Bool, Type.Bool ->
            let! setE = modelBoolExpr tvars set
                        |> mapMessages (curry BadExpr set)
            return func "BCAS" [dest |> blBefore; dest |> blAfter
                                test |> blBefore; test |> blAfter
                                setE |> BExpr |> before]
        | Type.Int, Type.Int ->
            let! setE = modelArithExpr tvars set
                        |> mapMessages (curry BadExpr set)
            return func "ICAS" [dest |> ilBefore; dest |> ilAfter
                                test |> ilBefore; test |> ilAfter
                                setE |> AExpr |> before]
        | _ ->
            // Oops, we have a type error.
            // Arbitrarily single out test as the cause of it.
            return! fail <| TypeMismatch(dtype, test, ttype)
    }

/// Converts an atomic fetch to a model command.
let modelFetch svars tvars dest src mode =
    (* First, determine whether we have a fetch from shared to thread
     * (a load), or a fetch from thread to shared (a store).
     * Also figure out whether we have a Boolean or arithmetic
     * version.
     * We figure this out by looking at dest.
     *)
    match dest with
    | VarIn svars Type.Int -> modelIntStore tvars dest src mode
    | VarIn svars Type.Bool -> modelBoolStore tvars dest src mode
    | VarIn tvars Type.Int -> modelIntLoad svars dest src mode
    | VarIn tvars Type.Bool -> modelBoolLoad svars dest src mode
    | lv -> fail (BadAVar(lv, NotFound(flattenLV lv)))

/// Converts a single atomic command from AST to part-commands.
let rec modelAtomic svars tvars =
    function
    | CompareAndSwap(dest, test, set) -> modelCAS svars tvars dest test set
    | Fetch(dest, src, mode) -> modelFetch svars tvars dest src mode
    | Postfix(operand, mode) ->
        (* A Postfix is basically a Fetch with no destination, at this point.
         * Thus, the source must be SHARED.
         * We don't allow the Direct fetch mode, as it is useless.
         *)
        trial {
            let! stype = lookupVar svars operand
                         |> mapMessages (curry BadSVar operand)
            // TODO(CaptainHayashi): sort out lvalues...
            let op = flattenLV operand
            match mode, stype with
            | Direct, _ ->
                return! fail Useless
            | Increment, Type.Bool -> return! fail (IncBool (LV operand))
            | Decrement, Type.Bool -> return! fail (DecBool (LV operand))
            | Increment, Type.Int ->
                return func "!I++" [op |> aBefore |> AExpr
                                    op |> aAfter |> AExpr]
            | Decrement, Type.Int ->
                return func "!I--" [op |> aBefore |> AExpr
                                    op |> aAfter |> AExpr]
        }
    | Id -> ok (func "Id" [])
    | Assume e ->
        modelBoolExpr tvars e
        |> mapMessages (curry BadExpr e)
        |> lift (BExpr >> Seq.singleton >> func "Assume")

/// Converts a local variable assignment to a Prim.
and modelAssign tvars l e =
    (* We model assignments as !ILSet or !BLSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial {
        let! ltype = l |> lookupVar tvars |> mapMessages (curry BadTVar l)
        match ltype with
        | Type.Bool -> let! em = e |> modelBoolExpr tvars
                                   |> mapMessages (curry BadExpr e)
                       return func "!BLSet" [ l |> blBefore; l |> blAfter
                                              em |> BExpr |> before ]
        | Type.Int -> let! em = modelArithExpr tvars e
                                |> mapMessages (curry BadExpr e)
                      return func "!ILSet" [ l |> ilBefore; l |> ilAfter
                                             em |> AExpr |> before ]
    }

/// Creates a partially resolved axiom for an if-then-else.
and modelITE protos svars tvars i t f =
    trial { let! iM = i |> modelBoolExpr tvars
                        |> mapMessages (curry BadITECondition i)
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
          (modelBoolExpr ls e |> mapMessages (curry BadWhileCondition e))
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
and modelCommand protos svars tvars =
    function
    | AST.Types.Command.Prim p -> modelPrim svars tvars p
    | If(i, t, e) -> modelITE protos svars tvars i t e
    | Command.While(e, b) -> modelWhile false protos svars tvars e b
    | DoWhile(b, e) -> modelWhile true protos svars tvars e b
    | c -> fail (CommandNotImplemented c)

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
    |> Seq.map snd
    |> findDuplicates
    |> Seq.toList
    |> function
       | [] -> ok proto
       | ds -> List.map (fun d -> VPEDuplicateParam(proto, d)) ds |> Bad

/// Checks a view prototype and converts it to an associative pair.
let modelViewProto proto =
    proto
    |> checkViewProtoDuplicates
    |> lift (fun pro -> (func pro.Name pro.Params, ()))
    |> mapMessages (curry BadVProto proto)

/// Checks view prototypes and converts them to func-table form.
let modelViewProtos protos =
    protos
    |> Seq.map modelViewProto
    |> collect
    |> lift Instantiate.makeFuncTable

/// Converts a collated script to a model.
let model collated : Result<UVModel<PMethod<ViewExpr<CView>>>, ModelError> =
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
