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
    | DFunc (s, pars) -> ok [ { VName = s; VParams = pars } ]
    | DUnit -> ok []
    | DJoin (l, r) -> joinViewDefs l r
/// Merges two sides of a view monoid in the AST into one multiset.
and joinViewDefs l r =
    lift2 (fun l r -> List.concat [ l; r ])
          (viewDefToSet l)
          (viewDefToSet r)

/// Flattens a LV to a string.
let rec flattenLV v =
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    match v with
    | LVIdent s -> s
    //| LVPtr vv -> "*" + flattenLV vv

/// Creates a reference to a Boolean lvalue.
/// This does NOT check to see if the lvalue exists!
let mkBoolLV (ctx: Context) lv =
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> ctx.MkBoolConst

/// Creates a reference to an integer lvalue.
/// This does NOT check to see if the lvalue exists!
let mkIntLV (ctx: Context) lv =
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> ctx.MkIntConst


/// Makes an And out of a pair of two expressions.
let mkAnd2 (ctx: Context) (l, r) = ctx.MkAnd [| l; r |]
/// Makes an Or out of a pair of two expressions.
let mkOr2 (ctx: Context) (l, r) = ctx.MkOr [| l; r |]
/// Makes an Add out of a pair of two expressions.
let mkAdd2 (ctx: Context) (l, r) = ctx.MkAdd [| l; r |]
/// Makes a Sub out of a pair of two expressions.
let mkSub2 (ctx: Context) (l, r) = ctx.MkSub [| l; r |]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 (ctx: Context) (l, r) = ctx.MkMul [| l; r |]

/// Converts a pair of arith-exps to Z3, then chains f onto them.
let rec chainArithExprs (ctx : Context)
    (f: (ArithExpr * ArithExpr) -> 'a)
    (pair: (AST.Expression * AST.Expression))
      : Result<'a, ExprError> =
    pairBindMap (arithExprToZ3 ctx) f pair

/// Converts a pair of bool-exps to Z3, then chains f onto them.
and chainBoolExprs ctx f = pairBindMap (boolExprToZ3 ctx) f

/// Converts a Starling Boolean expression to a Z3 predicate using
/// the given Z3 context.
and boolExprToZ3 (ctx: Context) expr =
    match expr with
    | TrueExp -> ctx.MkTrue () |> ok
    | FalseExp -> ctx.MkFalse () |> ok
    | LVExp v -> ctx.MkBoolConst ( flattenLV v ) |> ok
    | GtExp (l, r) -> chainArithExprs ctx (ctx.MkGt) (l, r)
    | GeExp (l, r) -> chainArithExprs ctx (ctx.MkGe) (l, r)
    | LeExp (l, r) -> chainArithExprs ctx (ctx.MkLe) (l, r)
    | LtExp (l, r) -> chainArithExprs ctx (ctx.MkLt) (l, r)
    | EqExp (l, r) -> chainBoolExprs ctx (ctx.MkEq) (l, r)
    | NeqExp (l, r) -> chainBoolExprs ctx (ctx.MkEq >> ctx.MkNot) (l, r)
    | AndExp (l, r) -> chainBoolExprs ctx (mkAnd2 ctx) (l, r)
    | OrExp (l, r) -> chainBoolExprs ctx (mkOr2 ctx) (l, r)
    | _ -> fail <| EEBadAST (expr, "cannot be a Boolean expression")

/// Converts a Starling arithmetic expression ot a Z3 predicate using
/// the given Z3 context.
and arithExprToZ3 (ctx: Context) expr =
    match expr with
    | IntExp i -> ((ctx.MkInt i) :> ArithExpr ) |> ok
    | LVExp v -> ((ctx.MkIntConst (flattenLV v)) :> ArithExpr) |> ok
    | MulExp (l, r) -> chainArithExprs ctx (mkMul2 ctx) (l, r)
    | DivExp (l, r) -> chainArithExprs ctx (ctx.MkDiv) (l, r)
    | AddExp (l, r) -> chainArithExprs ctx (mkAdd2 ctx) (l, r)
    | SubExp (l, r) -> chainArithExprs ctx (mkSub2 ctx) (l, r)
    | _ -> fail <| EEBadAST (expr, "cannot be an arithmetic expression")

/// Converts a single constraint to Z3.
let modelConstraint ctx c =
    trial { let! v = mapMessages CEView (viewDefToSet c.CView)
            let! c = mapMessages CEExpr (boolExprToZ3 ctx c.CExpression)
            return { CViews = v; CZ3 = c }}

/// Extracts the view constraints from a CollatedScript, turning each into a
/// Model.Constraint.
let modelConstraints ctx cs =
    List.map (modelConstraint ctx) cs.CConstraints |> collect

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
let makeVar (ctx : Context) ty (name : string) =
    match ty with
    | Int ->
        IntVar { VarExpr = ctx.MkIntConst name
                 VarPreExpr = ctx.MkIntConst (rewritePre name)
                 VarPostExpr = ctx.MkIntConst (rewritePost name)
                 VarFrameExpr = ctx.MkIntConst (rewriteFrame name) }
    | Bool ->
        BoolVar { VarExpr = ctx.MkBoolConst name
                  VarPreExpr = ctx.MkBoolConst (rewritePre name)
                  VarPostExpr = ctx.MkBoolConst (rewritePost name)
                  VarFrameExpr = ctx.MkBoolConst (rewriteFrame name) }

/// Converts a AST variable list to Var record lists.
let modelVarList (ctx : Context) lst =
    let names = List.map snd lst
    match (findDuplicates names) with
    | [] -> ok <| List.foldBack
                    (fun (ty, name) (map: VarMap) ->
                         map.Add (name, makeVar ctx ty name))
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
    lift2 (fun l r -> List.concat [ l; r ])
          (modelView ctx l)
          (modelView ctx r)
          ///
/// Converts a pair of AST views into a ConditionPair.
/// The pair is enclosed in a Chessie result.
let makeConditionPair ctx preAst postAst =
    lift2 (fun pre post -> { Pre = pre
                             Post = post } )
          (modelView ctx preAst)
          (modelView ctx postAst)

//
// Axioms
//

/// Retrieves the type of a Var.
let varType var =
    match var with
    | IntVar _ -> Int
    | BoolVar _ -> Bool

/// Looks up a variable record in an environment.
let lookupVar env lvalue =
    match lvalue with
    | LVIdent s -> Map.tryFind s env |> failIfNone (LENotFound s)
    //| _ -> LEBadLValue lvalue |> fail

/// Looks up a variable's type in an environment.
let lookupVarType env lvalue =
    lookupVar env lvalue |> lift varType

/// Lifts a Prim to an partially resolved axiom list.
let primToAxiom cpair prim = { Conditions = cpair
                               Inner = prim }
                             |> PAAxiom

/// Tries to look up the type of a local variable in an axiom context.
/// Returns a Chessie result; failures have AEBadLocal messages.
let lookupLocalType pmod lvalue =
    lookupVarType pmod.Locals lvalue |> mapMessages AEBadLocal

/// Tries to look up the type of a global variable in an axiom context.
/// Returns a Chessie result; failures have AEBadGlobal messages.
let lookupGlobalType pmod lvalue =
    lookupVarType pmod.Globals lvalue |> mapMessages AEBadGlobal

/// Converts a Boolean expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomBoolExprToZ3 pmod expr =
    boolExprToZ3 pmod.Context expr |> mapMessages AEBadExpr

/// Converts an arithmetic expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomArithExprToZ3 pmod expr =
    arithExprToZ3 pmod.Context expr |> mapMessages AEBadExpr

/// Converts an atomic action to a Prim.
let rec modelPrimOnAtomic pmod atom =
    match atom with
    | CompareAndSwap (dest, test, set) ->
        (* In a CAS, the destination must be GLOBAL;
         *           the tester and fail destination must be LOCAL;
         *           and the to-set value must be a valid expression.
         * dest, test, and set must agree on type.
         * The type of dest and test influences how we interpret set.
         *)
        trial { let! dtype = lookupGlobalType pmod dest
                let! ttype = lookupLocalType pmod test

                match dtype, ttype with
                | Bool, Bool ->
                    let! setz3 = axiomBoolExprToZ3 pmod set
                    // TODO(CaptainHayashi): test locality of c
                    return BoolCAS (dest, test, setz3)
                | Int, Int ->
                    let! setz3 = axiomArithExprToZ3 pmod set
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
        trial { let! dtype = lookupLocalType pmod dest
                let! stype = lookupGlobalType pmod src

                match dtype, stype, mode with
                | Int, Int, _ -> return ArithFetch (Some dest, src, mode)
                // For Booleans we cannot have a fetch mode other than Direct.
                | Bool, Bool, Direct -> return BoolFetch (dest, src)
                | Bool, Bool, Increment -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment a Boolean global")
                | Bool, Bool, Decrement -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement a Boolean global")
                | _ -> return! fail <| AETypeMismatch (dtype, src, stype) }
    | Postfix (operand, mode) ->
        (* A Postfix is basically a Fetch with no destination, at this point.
         * Thus, the source must be GLOBAL.
         * We don't allow the Direct fetch mode, as it is useless.
         *)
        trial { let! stype = lookupGlobalType pmod operand

                match mode, stype with
                | Direct, _ -> return! fail <| AEUnsupportedAtomic (atom, "<var>; has no effect; use <id>; or ; for no-ops")
                | Increment, Bool -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment a Boolean global")
                | Decrement, Bool -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement a Boolean global")
                | _, Int -> return ArithFetch (None, operand, mode) }
    | Id -> ok PrimId
    | Assume e -> axiomBoolExprToZ3 pmod e |> lift PrimAssume

/// Converts a local variable assignment to a Prim.
and modelPrimOnAssign pmod l e =
    (* We model assignments as ArithLocalSet or BoolLocalSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial { let! ltype = lookupLocalType pmod l
            match ltype with
            | Bool ->
                let! ez3 = axiomBoolExprToZ3 pmod e
                return BoolLocalSet (l, ez3)
            | Int ->
                let! ez3 = axiomArithExprToZ3 pmod e
                return ArithLocalSet (l, ez3)
          }

/// Creates a partially resolved axiom for an if-then-else.
and modelAxiomOnITE pmod outcond i t f =
    (* An ITE is not fully resolved yet.  We:
     * 0) Convert the if-statement into a Z3 expression;
     * 1) Place the ITE in the axioms pile;
     * 2) Merge in the axioms from the ‘then’ block;
     * 3) Merge in the axioms from the ‘else’ block.
     *)
    trial { let! iz3 = axiomBoolExprToZ3 pmod i
            (* We need to calculate the recursive axioms first, because we
             * need the inner cpairs for each to store the ITE placeholder.
             *)
            let! taxioms = modelAxiomsOnBlock pmod t
            let! faxioms = modelAxiomsOnBlock pmod f

            return PAITE (iz3, outcond, taxioms, faxioms) }

/// Converts a while or do-while to a partially-resolved axiom.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelAxiomOnWhile isDo pmod cpair e b =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    trial { let! ez3 = axiomBoolExprToZ3 pmod e
            let! baxioms = modelAxiomsOnBlock pmod b

            return PAWhile (isDo, ez3, cpair, baxioms) }

/// Converts a command and its precondition and postcondition to a
/// list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
and modelAxiomOnCommand pmod cpair cmd =
    match cmd with
    | Atomic a -> modelPrimOnAtomic pmod a |> lift (primToAxiom cpair)
    | Assign (l, e) -> modelPrimOnAssign pmod l e |> lift (primToAxiom cpair)
    | Skip -> modelPrimOnAtomic pmod Id |> lift (primToAxiom cpair)
    | If (i, t, e) -> modelAxiomOnITE pmod cpair i t e
    | While (e, b) -> modelAxiomOnWhile false pmod cpair e b
    | DoWhile (b, e) -> modelAxiomOnWhile true pmod cpair e b
    | c -> fail <| AEUnsupportedCommand (c, "TODO: implement")

/// Converts a precondition and postcondition to a condition pair, using
/// the given model and returning errors as AxiomErrors.
and makeAxiomConditionPair pmod pre post =
    makeConditionPair pmod.Context pre post
    |> mapMessages AEBadView

/// Converts a block to a Conditioned list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
and modelAxiomsOnBlock pmod block =
    (* We flip through every entry in the block, extracting its postcondition
     * and block.  At the same time, we hold onto the postcondition of the
     * _last_ entry (or the block precondition if we're at the first entry).
     *
     * Because the previous postcondition is this entry's precondition, we can
     * piece together the Hoare triple.  We also try to manipulate the command
     * into its representation in the model.
     * 
     * Supposing all of these steps worked, we can place the finished axiom
     * into the axioms list, and put the postcondition in place to serve as the
     * precondition for the next line.  Otherwise, our axiom list turns into a
     * failure.
     *)
    let bpost, axioms =
        List.foldBack
            (fun vcom state ->
                 let cmd = vcom.Command
                 let post = vcom.Post
                 (post, trial { let pre, axiomsR = state
                                // If our last axiomatisation failed, this will
                                // cause failure here.
                                let! axioms = axiomsR
                                let! cpair = makeAxiomConditionPair pmod pre post
                                let! axiom = modelAxiomOnCommand pmod cpair cmd
                                return axiom :: axioms } ))
            block.Contents
            (block.Pre, ok [])

    (* At the end of the above, we either have a list of axioms or an
     * error.  If we have the former, surround the axioms with the condition
     * pair derived from the precondition and postcondition of the block.
     *)
    trial { let! xs = axioms
            let! cpair = makeAxiomConditionPair pmod block.Pre bpost
            return { Conditions = cpair
                     Inner = xs }}

/// Converts a method to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
let modelAxiomsOnMethod pmod meth =
    // TODO(CaptainHayashi): method parameters
    modelAxiomsOnBlock pmod meth.Body
    |> lift (fun c -> c.Inner)

/// Converts a list of methods to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
let modelAxioms pmod methods =
    // TODO(CaptainHayashi): method parameters
    List.map (modelAxiomsOnMethod pmod) methods
    |> collect
    |> lift List.concat

/// Converts a collated script to a model with the given context.
let modelWith ctx collated =
    trial {
        let! globals = mapMessages MEVar (modelVarList ctx collated.CGlobals)
        let! locals = mapMessages MEVar (modelVarList ctx collated.CLocals)
        // TODO(CaptainHayashi): checking of constraints against locals and globals
        let! constraints = mapMessages MEConstraint (modelConstraints ctx collated)

        let pmod = { Context = ctx
                     Globals = globals
                     Locals = locals
                     DefViews = constraints
                     Axioms = () }

        let! axioms = mapMessages MEAxiom (modelAxioms pmod collated.CMethods)
        // TODO(CaptainHayashi): axioms, etc.

        return (withAxioms axioms pmod)
    }

/// Converts a collated script to a model.
let model = modelWith (new Context ())
    
