module Starling.Modeller

open System
open Microsoft.Z3

open Chessie.ErrorHandling

open Starling.AST
open Starling.Collator
open Starling.Model
open Starling.Errors.Modeller

/// Tries to flatten a view definition AST into a multiset.
let rec viewDefToSet vast =
    match vast with
    | DFunc ( s, pars ) -> ok [ { VName = s; VParams = pars } ]
    | DUnit -> ok []
    | DJoin ( l, r ) -> joinViewDefs l r
/// Merges two sides of a view monoid in the AST into one multiset.
and joinViewDefs l r =
    lift2 ( fun l r -> List.concat [ l; r ] )
          ( viewDefToSet l )
          ( viewDefToSet r )

/// Flattens a LV to a string.
let rec flattenLV v =
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    match v with
    | LVIdent s -> s
    | LVPtr vv -> "*" + flattenLV vv

/// Makes an And out of a pair of two expressions.
let mkAnd2 (ctx: Context) lr = ctx.MkAnd [| fst lr; snd lr |]
/// Makes an Or out of a pair of two expressions.
let mkOr2 (ctx: Context) lr = ctx.MkOr [| fst lr; snd lr |]
/// Makes an Add out of a pair of two expressions.
let mkAdd2 (ctx: Context) lr = ctx.MkAdd [| fst lr; snd lr |]
/// Makes a Sub out of a pair of two expressions.
let mkSub2 (ctx: Context) lr = ctx.MkSub [| fst lr; snd lr |]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 (ctx: Context) lr = ctx.MkMul [| fst lr; snd lr |]

/// Converts a pair of arith-exps to Z3, then chains f onto them.
let rec chainArithExprs ( ctx : Context )
    ( f : ( ArithExpr * ArithExpr ) -> 'a )
    ( pair : ( AST.Expression * AST.Expression ) )
      : Result<'a, ExprError> =
    pairBindMap ( arithExprToZ3 ctx ) f pair

/// Converts a pair of bool-exps to Z3, then chains f onto them.
and chainBoolExprs ctx f = pairBindMap ( boolExprToZ3 ctx ) f

/// Converts a Starling Boolean expression to a Z3 predicate using
/// the given Z3 context.
and boolExprToZ3 ( ctx : Context ) expr =
    match expr with
    | TrueExp -> ctx.MkTrue   () |> ok
    | FalseExp -> ctx.MkFalse  () |> ok
    | LVExp v -> ctx.MkBoolConst ( flattenLV v ) |> ok
    | GtExp ( l, r ) -> chainArithExprs ctx ( ctx.MkGt ) ( l, r )
    | GeExp ( l, r ) -> chainArithExprs ctx ( ctx.MkGe ) ( l, r )
    | LeExp ( l, r ) -> chainArithExprs ctx ( ctx.MkLe ) ( l, r )
    | LtExp ( l, r ) -> chainArithExprs ctx ( ctx.MkLt ) ( l, r )
    | EqExp ( l, r ) -> chainBoolExprs  ctx ( ctx.MkEq ) ( l, r )
    | NeqExp ( l, r ) -> chainBoolExprs  ctx ( ctx.MkEq >> ctx.MkNot ) ( l, r )
    | AndExp ( l, r ) -> chainBoolExprs  ctx ( mkAnd2 ctx ) ( l, r )
    | OrExp ( l, r ) -> chainBoolExprs  ctx ( mkOr2 ctx  ) ( l, r )
    | _ -> fail <| EEBadAST ( expr, "cannot be a Boolean expression" )

/// Converts a Starling arithmetic expression ot a Z3 predicate using
/// the given Z3 context.
and arithExprToZ3 ( ctx : Context ) expr =
    match expr with
    | IntExp i -> ( ( ctx.MkInt i ) :> ArithExpr ) |> ok
    | LVExp v -> ( ( ctx.MkIntConst ( flattenLV v ) ) :> ArithExpr ) |> ok
    | MulExp ( l, r ) -> chainArithExprs ctx ( mkMul2 ctx ) ( l, r )
    | DivExp ( l, r ) -> chainArithExprs ctx ( ctx.MkDiv ) ( l, r )
    | AddExp ( l, r ) -> chainArithExprs ctx ( mkAdd2 ctx ) ( l, r )
    | SubExp ( l, r ) -> chainArithExprs ctx ( mkSub2 ctx ) ( l, r )
    | _ -> fail <| EEBadAST ( expr, "cannot be an arithmetic expression" )

/// Extracts the view constraints from a CollatedScript, turning each into a
/// Model.Constraint.
let scriptViewConstraintsZ3 ctx cs =
    List.map (
      fun con -> trial {
        let! v = mapMessages CEView ( viewDefToSet con.CView )
        let! c = mapMessages CEExpr ( boolExprToZ3 ctx con.CExpression )
        return { CViews = v; CZ3 = c }
      }
    ) cs.CConstraints |> collect

/// Tries to find duplicate entries in a list.
/// Returns a list of the duplicates found.
let findDuplicates =
    List.groupBy id >> List.choose (function
                                    | ( _, [] ) | ( _, [_] ) -> None
                                    | ( x, _ ) -> Some x)

//
// Name rewrites
//

/// Rewrites the name of a constant to its pre-state form.
let rewritePre name = name + "!before"

/// Rewrites the name of a constant to its post-state form.
let rewritePost name = name + "!after"

/// Rewrites the name of a constant to its frame form.
let rewriteFrame name = name + "!r"


/// Converts a variable name and type to a Var.
let makeVar ( ctx : Context ) ty ( name : string ) =
    match ty with
    | Int ->
        IntVar { VarExpr = ctx.MkIntConst name
                 VarPreExpr = ctx.MkIntConst ( rewritePre name )
                 VarPostExpr = ctx.MkIntConst ( rewritePost name )
                 VarFrameExpr = ctx.MkIntConst ( rewriteFrame name ) }
    | Bool ->
        BoolVar { VarExpr = ctx.MkBoolConst name
                  VarPreExpr = ctx.MkBoolConst ( rewritePre name )
                  VarPostExpr = ctx.MkBoolConst ( rewritePost name )
                  VarFrameExpr = ctx.MkBoolConst ( rewriteFrame name ) }

/// Converts a AST variable list to Var record lists.
let modelVarList ( ctx : Context ) lst =
    let names = List.map snd lst
    match ( findDuplicates names ) with
    | [] -> ok <| List.foldBack
                    (fun x ( map : Map<string, Var> ) ->
                         map.Add ( snd x, makeVar ctx ( fst x ) ( snd x ) ))
                    lst
                    Map.empty
    | ds -> Bad <| List.map VEDuplicate ds

//
// View applications
//

/// Tries to flatten a view AST into a multiset.
let rec modelView ctx vast =
    match vast with
    | Func (s, pars) -> trial { let! pnames = List.map (function
                                                        | LVExp (LVIdent s) -> ok s
                                                        | _ -> VEUnsupported (vast, "arbitrary expressions not yet allowed here") |> fail)
                                                       pars
                                              |> collect
                                return [ CSetView { VName = s; VParams = pnames } ] }
    | IfView (e, l, r) -> trial { let! ez3 = boolExprToZ3 ctx e |> mapMessages ((curry VEBadExpr) vast)
                                  let! lvs = modelView ctx l
                                  let! rvs = modelView ctx r
                                  return [ CITEView (ez3, lvs, rvs) ] }
    | Unit -> ok []
    | Join (l, r) -> joinViews ctx l r
/// Merges two sides of a view monoid in the AST into one multiset.
and joinViews ctx l r =
    lift2 ( fun l r -> List.concat [ l; r ] )
          ( modelView ctx l )
          ( modelView ctx r )
          ///
/// Converts a pair of AST views into a ConditionPair.
/// The pair is enclosed in a Chessie result.
let makeConditionPair ctx preAst postAst =
    trial { let! pre = modelView ctx preAst
            let! post = modelView ctx postAst
            return { Pre = pre
                     Post = post }}

//
// Axioms
//

type AxiomContext =
    { ACtxZ3: Context
      ACtxLocals: Map<string, Var>
      ACtxGlobals: Map<string, Var>
      // TODO(CaptainHayashi): encode views as well.
    }

/// Retrieves the type of a Var.
let varType var =
    match var with
    | IntVar _ -> Int
    | BoolVar _ -> Bool

/// Looks up a variable record in an environment.
let lookupVar env lvalue =
    match lvalue with
    | LVIdent s -> Map.tryFind s env |> failIfNone ( LENotFound s )
    | _ -> LEBadLValue lvalue |> fail

/// Looks up a variable's type in an environment.
let lookupVarType env lvalue =
    lookupVar env lvalue |> lift varType

/// Lifts a Prim to an partially resolved axiom list.
let primToAxiom cpair prim = { AConditions = cpair
                               ACommand = [prim] }
                             |> PAAxiom

/// Tries to look up the type of a local variable in an axiom context.
/// Returns a Chessie result; failures have AEBadLocal messages.
let lookupLocalType actx lvalue =
    lookupVarType actx.ACtxLocals lvalue |> mapMessages AEBadLocal

/// Tries to look up the type of a global variable in an axiom context.
/// Returns a Chessie result; failures have AEBadGlobal messages.
let lookupGlobalType actx lvalue =
    lookupVarType actx.ACtxGlobals lvalue |> mapMessages AEBadGlobal

/// Converts a Boolean expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomBoolExprToZ3 actx expr =
    boolExprToZ3 actx.ACtxZ3 expr |> mapMessages AEBadExpr

/// Converts an arithmetic expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomArithExprToZ3 actx expr =
    arithExprToZ3 actx.ACtxZ3 expr |> mapMessages AEBadExpr

/// Extracts the precondition of a part-axiom.
let preOfPartAxiom pa =
    match pa with
    | PAAxiom a -> a.AConditions.Pre
    | PAWhile (_, _, o, _) -> o.Pre
    | PAITE (_, o, _, _) -> o.Pre

/// Extracts the postcondition of a part-axiom.
let postOfPartAxiom pa =
    match pa with
    | PAAxiom a -> a.AConditions.Post
    | PAWhile (_, _, o, _) -> o.Post
    | PAITE (_, o, _, _) -> o.Post

/// Extracts a condition pair from a list of part-axioms.
///
/// This pair is (P, Q), where {P}C{Q} and C is the sequential composition of
/// each command in the axiom list.
///
/// Less poetically, it is the precondition of the first command, and the
/// postcondition of the last command.
///
/// The result is optional, because C could be empty (and returning (true,
/// true) is not quite sound!).
let axiomsToConditionPair axioms =
    match axioms with
    | [] -> None
    | xs -> Some { Pre = preOfPartAxiom xs.[0]
                   Post = postOfPartAxiom xs.[List.length xs - 1] }

/// Converts an atomic action to a Prim.
let rec modelPrimOnAtomic actx atom =
    match atom with
    | CompareAndSwap (dest, test, set) ->
        (* In a CAS, the destination must be GLOBAL;
         *           the tester and fail destination must be LOCAL;
         *           and the to-set value must be a valid expression.
         * dest, test, and set must agree on type.
         * The type of dest and test influences how we interpret set.
         *)
        trial { let! dtype = lookupGlobalType actx dest
                let! ttype = lookupLocalType actx test

                match dtype, ttype with
                | Bool, Bool ->
                    let! setz3 = axiomBoolExprToZ3 actx set
                    // TODO(CaptainHayashi): test locality of c
                    return BoolCAS (dest, test, setz3)
                | Int, Int ->
                    let! setz3 = axiomArithExprToZ3 actx set
                    // TODO(CaptainHayashi): test locality of c
                    return ArithCAS (dest, test, setz3)
                | _ ->
                    // Oops, we have a type error.
                    // Arbitrarily single out test as the cause of it.
                    return! fail <| AETypeMismatch (dtype, test, ttype) }
    | Fetch (dest, src, mode) ->
        (* In a fetch, the destination must be LOCAL;
         *             the source must be GLOBAL;
         *             and the fetch mode can be any valid fetch mode.
         * dest and src must agree on type.
         *)
        trial { let! dtype = lookupLocalType actx dest
                let! stype = lookupGlobalType actx src

                match dtype, stype, mode with
                | Int, Int, _ -> return ArithFetch (Some dest, src, mode)
                // For Booleans we cannot have a fetch mode other than Direct.
                | Bool, Bool, Direct -> return BoolFetch (Some dest, src)
                | Bool, Bool, Increment -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment a Boolean global")
                | Bool, Bool, Decrement -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement a Boolean global")
                | _ -> return! fail <| AETypeMismatch (dtype, src, stype) }
    | Postfix (operand, mode) ->
        (* A Postfix is basically a Fetch with no destination, at this point.
         * Thus, the source must be GLOBAL.
         * We don't allow the Direct fetch mode, as it is useless.
         *)
        trial { let! stype = lookupGlobalType actx operand

                match mode, stype with
                | Direct, _ -> return! fail <| AEUnsupportedAtomic (atom, "<var>; has no effect; use <id>; or ; for no-ops")
                | Increment, Bool -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment a Boolean global")
                | Decrement, Bool -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement a Boolean global")
                | _, Int -> return ArithFetch (None, operand, mode) }
    | Id -> ok PrimId
    | Assume e -> axiomBoolExprToZ3 actx e |> lift PrimAssume

/// Converts a local variable assignment to a Prim.
and modelPrimOnAssign actx l e =
    (* We model assignments as ArithLocalSet or BoolLocalSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial { let! ltype = lookupLocalType actx l
            match ltype with
            | Bool ->
                let! ez3 = axiomBoolExprToZ3 actx e
                return BoolLocalSet (l, ez3)
            | Int ->
                let! ez3 = axiomArithExprToZ3 actx e
                return ArithLocalSet (l, ez3)
          }

/// Creates a partially resolved axiom for an if-then-else.
and modelAxiomOnITE actx outcond i t f =
    (* An ITE is not fully resolved yet.  We:
     * 0) Convert the if-statement into a Z3 expression;
     * 1) Place the ITE in the axioms pile;
     * 2) Merge in the axioms from the ‘then’ block;
     * 3) Merge in the axioms from the ‘else’ block.
     *)
    trial { let! iz3 = axiomBoolExprToZ3 actx i
            (* We need to calculate the recursive axioms first, because we
             * need the inner cpairs for each to store the ITE placeholder.
             *)
            let! taxioms = modelAxiomsOnBlock actx t
            let! faxioms = modelAxiomsOnBlock actx f

            return PAITE (iz3, outcond, taxioms, faxioms) }

/// Converts a while or do-while to a partially-resolved axiom.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelAxiomOnWhile isDo actx cpair e b =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    trial { let! ez3 = axiomBoolExprToZ3 actx e
            let! baxioms = modelAxiomsOnBlock actx b

            return PAWhile (isDo, ez3, cpair, baxioms) }

/// Converts a command and its precondition and postcondition to a
/// list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
and modelAxiomOnCommand actx cpair cmd =
    match cmd with
    | Atomic a -> modelPrimOnAtomic actx a |> lift (primToAxiom cpair)
    | Assign (l, e) -> modelPrimOnAssign actx l e |> lift (primToAxiom cpair)
    | Skip -> modelPrimOnAtomic actx Id |> lift (primToAxiom cpair)
    | If (i, t, e) -> modelAxiomOnITE actx cpair i t e
    | While (e, b) -> modelAxiomOnWhile false actx cpair e b
    | DoWhile (b, e) -> modelAxiomOnWhile true actx cpair e b
    | c -> fail <| AEUnsupportedCommand (c, "TODO: implement")

/// Converts a block to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
and modelAxiomsOnBlock actx block =
    List.foldBack
        (fun vcom state ->
             let cmd = vcom.Command
             let post = vcom.Post
             (post, trial { let pre, axiomsR = state
                            let! axioms = axiomsR
                            let! cpair = makeConditionPair actx.ACtxZ3 pre post
                                         |> mapMessages AEBadView
                            let! axiom = modelAxiomOnCommand actx cpair cmd
                            return axiom :: axioms } ))
        block.Contents
        (block.Pre, ok [])
    |> snd

/// Converts a method to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
let modelAxiomsOnMethod actx meth =
    // TODO(CaptainHayashi): method parameters
    modelAxiomsOnBlock actx meth.Body

/// Converts a list of methods to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
let modelAxioms ctx globals locals methods =
    let actx = { ACtxZ3 = ctx
                 ACtxGlobals = globals
                 ACtxLocals = locals }
    // TODO(CaptainHayashi): method parameters
    List.map (modelAxiomsOnMethod actx) methods
    |> collect
    |> lift List.concat

/// Converts a collated script to a model.
let model ctx collated =
    trial {
        let! globals = mapMessages MEVar ( modelVarList ctx collated.CGlobals )
        let! locals = mapMessages MEVar ( modelVarList ctx collated.CLocals )
        // TODO(CaptainHayashi): checking of constraints against locals and globals
        let! constraints = mapMessages MEConstraint ( scriptViewConstraintsZ3 ctx collated )
        let! axioms = mapMessages MEAxiom ( modelAxioms ctx globals locals collated.CMethods )
        // TODO(CaptainHayashi): axioms, etc.

        return { Context = ctx
                 Globals = globals
                 Locals = locals
                 DefViews = constraints
                 Axioms = axioms }
    }
