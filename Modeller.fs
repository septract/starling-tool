module Starling.Modeller

open System
open Microsoft.Z3

open Chessie.ErrorHandling

open Starling.Var
open Starling.AST
open Starling.Collator
open Starling.Model
open Starling.Errors.Modeller

let (|ArithOp|BoolOp|) bop =
    match bop with
    | Mul -> ArithOp
    | Div -> ArithOp
    | Add -> ArithOp
    | Sub -> ArithOp
    | Gt -> BoolOp
    | Ge -> BoolOp
    | Le -> BoolOp
    | Lt -> BoolOp
    | Eq -> BoolOp
    | Neq -> BoolOp
    | And -> BoolOp
    | Or -> BoolOp

let (|ArithIn|BoolIn|AnyIn|) bop =
    match bop with
    | Mul -> ArithIn
    | Div -> ArithIn
    | Add -> ArithIn
    | Sub -> ArithIn
    | Gt -> ArithIn
    | Ge -> ArithIn
    | Le -> ArithIn
    | Lt -> ArithIn
    | Eq -> AnyIn
    | Neq -> AnyIn
    | And -> BoolIn
    | Or -> BoolIn

/// Tries to flatten a view definition AST into a multiset.
let rec viewDefToSet vast =
    match vast with
    | DFunc (s, pars) -> [ { VName = s; VParams = pars } ]
    | DUnit -> []
    | DJoin (l, r) -> joinViewDefs l r
/// Merges two sides of a view monoid in the AST into one multiset.
and joinViewDefs l r =
     List.concat [viewDefToSet l
                  viewDefToSet r]

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
let rec chainArithExprs (model: Model<'a, 'b>)
    (f: (ArithExpr * ArithExpr) -> 'a)
    (pair: (AST.Expression * AST.Expression))
      : Result<'a, ExprError> =
    pairBindMap (arithExprToZ3 model) f pair

/// Converts a pair of bool-exps to Z3, then chains f onto them.
and chainBoolExprs model f = pairBindMap (boolExprToZ3 model) f

/// Converts a Starling Boolean expression to a Z3 predicate using
/// the given Z3 context.
and boolExprToZ3 model expr =
    let ctx = model.Context
    match expr with
    | TrueExp -> ctx.MkTrue () |> ok
    | FalseExp -> ctx.MkFalse () |> ok
    | LVExp v -> ctx.MkBoolConst ( flattenLV v ) |> ok
    | BopExp (BoolOp as op, l, r) ->
        match op with
            | ArithIn as o ->
                trial {let! lA = arithExprToZ3 model l
                       let! rA = arithExprToZ3 model r
                       return (match o with
                               | Gt -> ctx.MkGt
                               | Ge -> ctx.MkGe
                               | Le -> ctx.MkLe
                               | Lt -> ctx.MkLt
                               | _  -> failwith "unreachable") (lA, rA) }
            | BoolIn as o ->
                trial {let! lB = boolExprToZ3 model l
                       let! rB = boolExprToZ3 model r
                       return (match o with
                               | And -> mkAnd2 ctx
                               | Or -> mkOr2 ctx
                               | _  -> failwith "unreachable") (lB, rB) }
            | AnyIn as o ->
                // TODO(CaptainHayashi): don't infer bool here.
                trial {let! lE = boolExprToZ3 model l
                       let! rE = boolExprToZ3 model r
                       return (match o with
                               | Eq -> ctx.MkEq
                               | Neq -> (ctx.MkEq >> ctx.MkNot)
                               | _  -> failwith "unreachable") (lE, rE) }
    | _ -> fail <| EEBadAST (expr, "cannot be a Boolean expression")

/// Converts a Starling arithmetic expression ot a Z3 predicate using
/// the given Z3 context.
and arithExprToZ3 model expr =
    let ctx = model.Context
    match expr with
    | IntExp i -> ((ctx.MkInt i) :> ArithExpr ) |> ok
    | LVExp v -> ((ctx.MkIntConst (flattenLV v)) :> ArithExpr) |> ok
    | BopExp (ArithOp & op, l, r) ->
        trial { let! lA = arithExprToZ3 model l
                let! rA = arithExprToZ3 model r
                return (match op with
                        | Mul -> mkMul2 ctx
                        | Div -> ctx.MkDiv
                        | Add -> mkAdd2 ctx
                        | Sub -> mkSub2 ctx
                        | _  -> failwith "unreachable") (lA, rA) }
    | _ -> fail <| EEBadAST (expr, "cannot be an arithmetic expression")

/// Merges a list of prototype and definition parameters into one environment,
/// binding the types from the former to the names from the latter.
let funcViewEnvMerge ctx ppars dpars =
    List.map2
        (fun (ty, _) name -> (name, makeVar ctx ty name))
        ppars
        dpars
    |> Map.ofList

/// Produces the environment created by interpreting the functional view with
/// name name and params dpars, using the view prototype map vpm.
let envOfFuncViewDef ctx vpm name dpars =
    // Does this functional view name a proper view?
    match Map.tryFind name vpm with
    | Some ppars ->
        // Does it have the correct number of parameters?
        let ldpars = List.length dpars
        let lppars = List.length ppars
        if ldpars <> lppars
        then fail <| VDEBadParamCount (name, lppars, ldpars)
        else ok <| funcViewEnvMerge ctx ppars dpars
    | None -> fail <| VDENoSuchView name

     

/// Produces the environment created by interpreting the viewdef vd using the
/// view prototype map vpm.
let rec envOfViewDef ctx vpm vd =
    match vd with
    | DUnit -> ok Map.empty
    | DFunc (v, pars) -> envOfFuncViewDef ctx vpm v pars
    | DJoin (l, r) -> trial {let! lE = envOfViewDef ctx vpm l
                             let! rE = envOfViewDef ctx vpm r
                             return! combineMaps lE rE |> mapMessages VDEBadVars}

/// Produces the variable environment for the constraint c.
let envOfConstraint model c =
    envOfViewDef model.Context model.VProtos c.CView
    |> bind (combineMaps model.Globals >> mapMessages VDEGlobalVarConflict)

/// Converts a single constraint to Z3.
let modelConstraint model c =
    let ctx = model.Context
    trial {let! e = mapMessages CEView (envOfConstraint model c)
           let v = viewDefToSet c.CView
           let! c = mapMessages CEExpr (boolExprToZ3 model c.CExpression)
           return {CViews = v
                   CZ3 = c}}

/// Extracts the view constraints from a CollatedScript, turning each into a
/// Model.Constraint.
let modelConstraints model cs =
    List.map (modelConstraint model) cs.CConstraints |> collect

//
// View applications
//

/// Tries to flatten a view AST into a multiset.
let rec modelView ctx vast =
    match vast with
    | Func (s, pars) -> trial {let! pnames = List.map (function
                                                       | LVExp (LVIdent s) -> ok s
                                                       | _ -> VEUnsupported (vast, "arbitrary expressions not yet allowed here") |> fail)
                                                      pars
                                             |> collect
                               return [CSetView {VName = s
                                                 VParams = pnames} ] }
    | IfView (e, l, r) -> trial {let! ez3 = boolExprToZ3 ctx e |> mapMessages ((curry VEBadExpr) vast)
                                 let! lvs = modelView ctx l
                                 let! rvs = modelView ctx r
                                 return [CITEView (ez3, lvs, rvs) ] }
    | Unit -> ok []
    | Join (l, r) -> joinViews ctx l r
/// Merges two sides of a view monoid in the AST into one multiset.
and joinViews ctx l r =
    lift2 (List.append)
          (modelView ctx l)
          (modelView ctx r)
/// Converts a pair of AST views into a ConditionPair.
/// The pair is enclosed in a Chessie result.
let makeConditionPair ctx preAst postAst =
    lift2 (fun pre post -> {Pre = pre
                            Post = post} )
          (modelView ctx preAst)
          (modelView ctx postAst)

//
// Axioms
//

/// Lifts a Prim to an partially resolved axiom list.
let primToAxiom cpair prim = {Conditions = cpair
                              Inner = prim}
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
    boolExprToZ3 pmod expr |> mapMessages AEBadExpr

/// Converts an arithmetic expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomArithExprToZ3 pmod expr =
    arithExprToZ3 pmod expr |> mapMessages AEBadExpr

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
        trial {let! dtype = lookupGlobalType pmod dest
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
        trial {let! dtype = lookupLocalType pmod dest
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
        trial {let! stype = lookupGlobalType pmod operand

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
    trial {let! ltype = lookupLocalType pmod l
           match ltype with
           | Bool ->
               let! ez3 = axiomBoolExprToZ3 pmod e
               return BoolLocalSet (l, ez3)
           | Int ->
               let! ez3 = axiomArithExprToZ3 pmod e
               return ArithLocalSet (l, ez3) }

/// Creates a partially resolved axiom for an if-then-else.
and modelAxiomOnITE pmod outcond i t f =
    (* An ITE is not fully resolved yet.  We:
     * 0) Convert the if-statement into a Z3 expression;
     * 1) Place the ITE in the axioms pile;
     * 2) Merge in the axioms from the ‘then’ block;
     * 3) Merge in the axioms from the ‘else’ block.
     *)
    trial {let! iz3 = axiomBoolExprToZ3 pmod i
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
    trial {let! ez3 = axiomBoolExprToZ3 pmod e
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
    makeConditionPair pmod pre post
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
                 (post, trial {let pre, axiomsR = state
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
    trial {let! xs = axioms
           let! cpair = makeAxiomConditionPair pmod block.Pre bpost
           return {Conditions = cpair
                   Inner = xs}}

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

/// Checks a view prototype to see if it contains duplicate parameters.
let checkViewProtoDuplicates proto =
    let names = List.map snd proto.VPPars
    match (findDuplicates names) with
    | [] -> ok proto
    | ds -> Bad <| List.map (fun d -> VPEDuplicateParam (proto, d)) ds

/// Checks a view prototype and converts it to an associative pair.
let modelViewProto proto =
    proto
    |> checkViewProtoDuplicates
    |> lift (fun pro -> (pro.VPName, pro.VPPars))

/// Checks view prototypes and converts them to map form.
let modelViewProtos protos =
    protos
    |> Seq.ofList
    |> Seq.map modelViewProto
    |> collect
    |> lift Map.ofSeq

/// Converts a collated script to a model with the given context.
let modelWith ctx collated =
    trial {let! vprotos = mapMessages MEVProto (modelViewProtos collated.CVProtos)
           let! globals = mapMessages MEVar (makeVarMap ctx collated.CGlobals)
           let! locals = mapMessages MEVar (makeVarMap ctx collated.CLocals)
           let! allvars = mapMessages MEVar (combineMaps locals globals)

           let imod = {Context = ctx
                       Globals = globals
                       Locals = locals
                       AllVars = allvars
                       VProtos = vprotos
                       DefViews = ()
                       Axioms = () }

           // TODO(CaptainHayashi): checking of constraints against locals and globals
           let! constraints = mapMessages MEConstraint (modelConstraints imod collated)

           let pmod = {Context = ctx
                       Globals = globals
                       Locals = locals
                       AllVars = allvars
                       VProtos = vprotos
                       DefViews = constraints
                       Axioms = () }

           let! axioms = mapMessages MEAxiom (modelAxioms pmod collated.CMethods)
           // TODO(CaptainHayashi): axioms, etc.

           return (withAxioms axioms pmod) }

/// Converts a collated script to a model.
let model = modelWith (new Context ())
    
