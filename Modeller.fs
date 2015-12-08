module Starling.Modeller

open System
open Microsoft.Z3

open Chessie.ErrorHandling

open Starling.Z3
open Starling.Var
open Starling.Errors.Var
open Starling.AST
open Starling.Collator
open Starling.Model
open Starling.Errors.Modeller

(*
 * Expression classification
 *)

/// Active pattern classifying bops as to whether they create
/// arithmetic or Boolean expressions.
let (|ArithOp|BoolOp|) bop =
    match bop with
    | Mul | Div | Add | Sub -> ArithOp
    | Gt | Ge | Le | Lt -> BoolOp
    | Eq | Neq -> BoolOp
    | And | Or -> BoolOp

/// Active pattern classifying bops as to whether they take in
/// arithmetic, Boolean, or indeterminate operands.
let (|ArithIn|BoolIn|AnyIn|) bop =
    match bop with
    | Mul | Div | Add | Sub -> ArithIn
    | Gt | Ge | Le | Lt -> ArithIn
    | Eq | Neq -> AnyIn
    | And | Or -> BoolIn

/// Active pattern classifying expressions as to whether they are
/// arithmetic, Boolean, or indeterminate.
let (|BoolExp|ArithExp|AnyExp|) expr =
    match expr with
    | LVExp _ -> AnyExp
    | IntExp _ -> ArithExp
    | TrueExp | FalseExp -> BoolExp
    | BopExp (BoolOp, _, _) -> BoolExp
    | BopExp (ArithOp, _, _) -> ArithExp

(*
 * Expression translation
 *)

/// Converts a Starling expression of ambiguous type to a Z3 predicate using
/// the given partial model and environment.
let rec anyExprToZ3 model env expr =
    let ctx = model.Context
    match expr with
    (* First, if we have a variable, the type of expression is
     * determined by the type of the variable.
     *)
    | LVExp v ->
        (* Look-up the variable to ensure it a) exists and b) is of a
         * Boolean type.
         *)
        trial {let! vt = lookupVar env v
                         |> mapMessages ((curry EEVar) expr)
               match vt with
               | BoolVar _ -> return (mkBoolLV ctx v) :> Expr
               | IntVar _ -> return (mkIntLV ctx v) :> Expr}
    (* We can use the active patterns above to figure out whether we
     * need to treat this expression as arithmetic or Boolean.
     *)
    | ArithExp -> arithExprToZ3 model env expr |> lift (fun e -> e :> Expr)
    | BoolExp -> boolExprToZ3 model env expr |> lift (fun e -> e :> Expr)
    | _ -> failwith "unreachable"

/// Converts a Starling Boolean expression to a Z3 predicate using
/// the given partial model and environment.
and boolExprToZ3 model env expr =
    let ctx = model.Context
    match expr with
    | TrueExp -> ctx.MkTrue () |> ok
    | FalseExp -> ctx.MkFalse () |> ok
    | LVExp v ->
        (* Look-up the variable to ensure it a) exists and b) is of a
         * Boolean type.
         *)
        trial {let! vt = lookupVar env v
                         |> mapMessages ((curry EEVar) expr)
               match vt with
               | BoolVar _ -> return (mkBoolLV ctx v)
               | _ -> return! (fail <| EEVarNotBoolean v) }
    | BopExp (BoolOp as op, l, r) ->
        match op with
            | ArithIn as o ->
                trial {let! lA = arithExprToZ3 model env l
                       let! rA = arithExprToZ3 model env r
                       return (match o with
                               | Gt -> mkGt
                               | Ge -> mkGe
                               | Le -> mkLe
                               | Lt -> mkLt
                               | _  -> failwith "unreachable") ctx lA rA }
            | BoolIn as o ->
                trial {let! lB = boolExprToZ3 model env l
                       let! rB = boolExprToZ3 model env r
                       return (match o with
                               | And -> mkAnd2
                               | Or -> mkOr2
                               | _  -> failwith "unreachable") ctx lB rB }
            | AnyIn as o ->
                // TODO(CaptainHayashi): don't infer bool here.
                trial {let! lE = anyExprToZ3 model env l
                       let! rE = anyExprToZ3 model env r
                       return (match o with
                               | Eq -> mkEq
                               | Neq -> mkNeq
                               | _  -> failwith "unreachable") ctx lE rE }
    | _ -> fail <| EEBadAST (expr, "cannot be a Boolean expression")

/// Converts a Starling arithmetic expression ot a Z3 predicate using
/// the given Z3 context.
and arithExprToZ3 model env expr =
    let ctx = model.Context
    match expr with
    | IntExp i -> ((ctx.MkInt i) :> ArithExpr ) |> ok
    | LVExp v ->
        (* Look-up the variable to ensure it a) exists and b) is of an
         * arithmetic type.
         *)
        trial {let! vt = lookupVar env v
                         |> mapMessages ((curry EEVar) expr)
               match vt with
               | IntVar _ -> return (mkIntLV ctx v) :> ArithExpr
               | _ -> return! (fail <| EEVarNotArith v) }
    | BopExp (ArithOp as op, l, r) ->
        trial {let! lA = arithExprToZ3 model env l
               let! rA = arithExprToZ3 model env r
               return (match op with
                       | Mul -> mkMul2
                       | Div -> mkDiv
                       | Add -> mkAdd2
                       | Sub -> mkSub2
                       | _  -> failwith "unreachable") ctx lA rA }
    | _ -> fail <| EEBadAST (expr, "cannot be an arithmetic expression")


(*
 * View definitions
 *)

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


(*
 * Views
 *)

/// Merges a list of prototype and definition parameters into one list,
/// binding the types from the former to the names from the latter.
let funcViewParMerge ppars dpars =
    List.map2
        (fun (ty, _) name -> (ty, name))
        ppars
        dpars

/// Produces the environment created by interpreting the functional view with
/// name name and params dpars, using the view prototype map vpm.
let modelFuncViewDef ctx vpm name dpars =
    // Does this functional view name a proper view?
    match Map.tryFind name vpm with
    | Some ppars ->
        // Does it have the correct number of parameters?
        let ldpars = List.length dpars
        let lppars = List.length ppars
        if ldpars <> lppars
        then fail <| VDEBadParamCount (name, lppars, ldpars)
        else ok <| [ {VName = name
                      VParams = funcViewParMerge ppars dpars} ]
    | None -> fail <| VDENoSuchView name

/// Tries to convert a view def into its model (multiset) form.
let rec modelViewDef model vd =
    let ctx = model.Context
    let vpm = model.VProtos

    match vd with
    | DUnit -> ok []
    | DFunc (v, pars) -> modelFuncViewDef ctx vpm v pars
    | DJoin (l, r) -> trial {let! lM = modelViewDef model l
                             let! rM = modelViewDef model r
                             return List.append lM rM}

/// Produces the environment created by interpreting the viewdef vds using the
/// view prototype map vpm.
let rec envOfViewDef ctx vds =
    vds
    |> Seq.ofList
    |> Seq.map (fun vd -> makeVarMap ctx vd.VParams)
    |> seqBind (fun xR s -> bind (combineMaps s) xR) Map.empty
    |> mapMessages VDEBadVars

/// Produces the variable environment for the constraint whose viewdef is v.
let envOfConstraint model v =
    envOfViewDef model.Context v
    |> bind (combineMaps model.Globals >> mapMessages VDEGlobalVarConflict)

/// Converts a single constraint to Z3.
let modelConstraint model c =
    let ctx = model.Context
    trial {let! v = modelViewDef model c.CView |> mapMessages CEView
           let! e = envOfConstraint model v |> mapMessages CEView
           let! c = boolExprToZ3 model e c.CExpression |> mapMessages CEExpr 
           return {CViews = List.sort v
                   CZ3 = c}}

/// Extracts the view constraints from a CollatedScript, turning each into a
/// Model.Constraint.
let modelConstraints model cs =
    List.map (modelConstraint model) cs.CConstraints |> collect

//
// View applications
//

/// Tries to flatten a view AST into a multiset.
let rec modelView model vast =
    match vast with
    | Func (s, pars) -> trial {let! pexps = pars
                                            |> List.map (anyExprToZ3 model model.Locals
                                                         >> mapMessages (curry VEBadExpr vast))
                                            |> collect
                               return [CSetView {VName = s
                                                 VParams = pexps} ] }
    | IfView (e, l, r) -> trial {let! ez3 = boolExprToZ3 model model.Locals e |> mapMessages ((curry VEBadExpr) vast)
                                 let! lvs = modelView model l
                                 let! rvs = modelView model r
                                 return [CITEView (ez3, lvs, rvs) ] }
    | Unit -> ok []
    | Join (l, r) -> joinViews model l r
/// Merges two sides of a view monoid in the AST into one multiset.
and joinViews model l r =
    lift2 (List.append)
          (modelView model l)
          (modelView model r)
/// Converts a pair of AST views into a ConditionPair.
/// The pair is enclosed in a Chessie result.
let makeConditionPair model preAst postAst =
    lift2 (fun pre post -> {Pre = pre
                            Post = post} )
          (modelView model preAst)
          (modelView model postAst)

//
// Axioms
//

/// Lifts a Prim to an partially resolved axiom list.
let primToAxiom cpair prim = {Conditions = cpair
                              Inner = prim}
                             |> PAAxiom

let (|GlobalVar|_|) model (lvalue: Var.LValue) =
    tryLookupVar model.Globals lvalue

let (|LocalVar|_|) model (lvalue: Var.LValue) =
    tryLookupVar model.Locals lvalue

/// Tries to look up the type of a local variable in an axiom context.
/// Returns a Chessie result; failures have AEBadLocal messages.
let lookupLocalType model lvalue =
    match lvalue with
    | LocalVar model v -> varType v |> ok
    | _ -> VMENotFound (flattenLV lvalue) |> AEBadLocal |> fail

/// Tries to look up the type of a global variable in an axiom context.
/// Returns a Chessie result; failures have AEBadGlobal messages.
let lookupGlobalType model lvalue =
    match lvalue with
    | GlobalVar model v -> varType v |> ok
    | _ -> VMENotFound (flattenLV lvalue) |> AEBadLocal |> fail

/// Converts a Boolean expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomBoolExprToZ3 model expr =
    boolExprToZ3 model model.Locals expr |> mapMessages AEBadExpr

/// Converts an arithmetic expression to z3 within the given axiom context.
/// Returns a Chessie result; failures have AEBadExpr messages.
let axiomArithExprToZ3 model expr =
    arithExprToZ3 model model.Locals expr |> mapMessages AEBadExpr

/// Converts a Boolean load to a Prim.
let modelPrimOnBoolLoad model atom dest src mode =
    (* In a Boolean load, the destination must be LOCAL and Boolean;
     *                    the source must be a GLOBAL Boolean lvalue;
     *                    and the fetch mode must be Direct.
     *)
    match src with
    | LVExp s ->
        trial {let! stype = lookupGlobalType model s

               match stype, mode with
               | Bool, Direct -> return BoolLoad (dest, s)
               | Bool, Increment -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment a Boolean global")
               | Bool, Decrement -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement a Boolean global")
               | _ -> return! fail <| AETypeMismatch (Bool, s, stype) }
    | _ -> fail <| AEUnsupportedAtomic (atom, "loads must have a lvalue source")

/// Converts an integer load to a Prim.
let modelPrimOnIntLoad model atom dest src mode =
    (* In a Boolean load, the destination must be LOCAL and Boolean;
     *                    the source must be a GLOBAL arithmetic lvalue;
     *                    and the fetch mode is unconstrained.
     *)
    match src with
    | LVExp s ->
        trial {let! stype = lookupGlobalType model s

               match stype, mode with
               | Int, _ -> return IntLoad (Some dest, s, mode)
               | _ -> return! fail <| AETypeMismatch (Int, s, stype) }
    | _ -> fail <| AEUnsupportedAtomic (atom, "loads must have a lvalue source")

/// Converts a Boolean store to a Prim.
let modelPrimOnBoolStore model atom dest src mode =
    (* In a Boolean store, the destination must be GLOBAL and Boolean;
     *                     the source must be LOCAL and Boolean;
     *                     and the fetch mode must be Direct.
     *)
    trial {let! sxp = axiomBoolExprToZ3 model src

           match mode with
           | Direct -> return BoolStore (dest, sxp)
           | Increment -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment an expression")
           | Decrement -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement an expression") }

/// Converts an integral store to a Prim.
let modelPrimOnIntStore model atom dest src mode =
    (* In an integral store, the destination must be GLOBAL and integral;
     *                       the source must be LOCAL and integral;
     *                       and the fetch mode must be Direct.
     *)
    trial {let! sxp = axiomArithExprToZ3 model src

           match mode with
           | Direct -> return IntStore (dest, sxp)
           | Increment -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment an expression")
           | Decrement -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement an expression") }

/// Converts an atomic action to a Prim.
let rec modelPrimOnAtomic model atom =
    match atom with
    | CompareAndSwap (dest, test, set) ->
        (* In a CAS, the destination must be GLOBAL;
         *           the tester and fail destination must be LOCAL;
         *           and the to-set value must be a valid expression.
         * dest, test, and set must agree on type.
         * The type of dest and test influences how we interpret set.
         *)
        trial {let! dtype = lookupGlobalType model dest
               let! ttype = lookupLocalType model test

               match dtype, ttype with
               | Bool, Bool ->
                   let! setz3 = axiomBoolExprToZ3 model set
                   // TODO(CaptainHayashi): test locality of c
                   return BoolCAS (dest, test, setz3)
               | Int, Int ->
                   let! setz3 = axiomArithExprToZ3 model set
                   // TODO(CaptainHayashi): test locality of c
                   return IntCAS (dest, test, setz3)
               | _ ->
                   // Oops, we have a type error.
                   // Arbitrarily single out test as the cause of it.
                   return! fail <| AETypeMismatch (dtype, test, ttype) }
    | Fetch (dest, src, mode) ->
        (* First, determine whether we have a fetch from global to local
         * (a load), or a fetch from local to global (a store).
         * Also figure out whether we have a Boolean or arithmetic
         * version.
         * We figure this out by looking at dest.
         *)
        match dest with
        | GlobalVar model (IntVar _) -> modelPrimOnIntStore model atom dest src mode
        | GlobalVar model (BoolVar _) -> modelPrimOnBoolStore model atom dest src mode
        | LocalVar model (IntVar _) -> modelPrimOnIntLoad model atom dest src mode
        | LocalVar model (BoolVar _) -> modelPrimOnBoolLoad model atom dest src mode
        // TODO(CaptainHayashi): incorrect error here.
        | _ -> fail <| AEBadGlobal (VMENotFound (flattenLV dest))
    | Postfix (operand, mode) ->
        (* A Postfix is basically a Fetch with no destination, at this point.
         * Thus, the source must be GLOBAL.
         * We don't allow the Direct fetch mode, as it is useless.
         *)
        trial {let! stype = lookupGlobalType model operand

               match mode, stype with
               | Direct, _ -> return! fail <| AEUnsupportedAtomic (atom, "<var>; has no effect; use <id>; or ; for no-ops")
               | Increment, Bool -> return! fail <| AEUnsupportedAtomic (atom, "cannot increment a Boolean global")
               | Decrement, Bool -> return! fail <| AEUnsupportedAtomic (atom, "cannot decrement a Boolean global")
               | _, Int -> return IntLoad (None, operand, mode) }
    | Id -> ok PrimId
    | Assume e -> axiomBoolExprToZ3 model e |> lift PrimAssume

/// Converts a local variable assignment to a Prim.
and modelPrimOnAssign model l e =
    (* We model assignments as IntLocalSet or BoolLocalSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial {let! ltype = lookupLocalType model l
           match ltype with
           | Bool ->
               let! ez3 = axiomBoolExprToZ3 model e
               return BoolLocalSet (l, ez3)
           | Int ->
               let! ez3 = axiomArithExprToZ3 model e
               return IntLocalSet (l, ez3) }

/// Creates a partially resolved axiom for an if-then-else.
and modelAxiomOnITE model outcond i t f =
    (* An ITE is not fully resolved yet.  We:
     * 0) Convert the if-statement into a Z3 expression;
     * 1) Place the ITE in the axioms pile;
     * 2) Merge in the axioms from the ‘then’ block;
     * 3) Merge in the axioms from the ‘else’ block.
     *)
    trial {let! iz3 = axiomBoolExprToZ3 model i
           (* We need to calculate the recursive axioms first, because we
            * need the inner cpairs for each to store the ITE placeholder.
            *)
           let! taxioms = modelAxiomsOnBlock model t
           let! faxioms = modelAxiomsOnBlock model f

           return PAITE (iz3, outcond, taxioms, faxioms) }

/// Converts a while or do-while to a partially-resolved axiom.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelAxiomOnWhile isDo model cpair e b =
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    trial {let! ez3 = axiomBoolExprToZ3 model e
           let! baxioms = modelAxiomsOnBlock model b

           return PAWhile (isDo, ez3, cpair, baxioms) }

/// Converts a command and its precondition and postcondition to a
/// list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
and modelAxiomOnCommand model cpair cmd =
    match cmd with
    | Atomic a -> modelPrimOnAtomic model a |> lift (primToAxiom cpair)
    | Assign (l, e) -> modelPrimOnAssign model l e |> lift (primToAxiom cpair)
    | Skip -> modelPrimOnAtomic model Id |> lift (primToAxiom cpair)
    | If (i, t, e) -> modelAxiomOnITE model cpair i t e
    | While (e, b) -> modelAxiomOnWhile false model cpair e b
    | DoWhile (b, e) -> modelAxiomOnWhile true model cpair e b
    | c -> fail <| AEUnsupportedCommand (c, "TODO: implement")

/// Converts a precondition and postcondition to a condition pair, using
/// the given model and returning errors as AxiomErrors.
and makeAxiomConditionPair model pre post =
    makeConditionPair model pre post
    |> mapMessages AEBadView

/// Converts a block to a Conditioned list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
and modelAxiomsOnBlock model block =
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
        (* Currently, we fold forwards and then reverse the axioms list.  This
         * is because backwards folding means that we're stepping through the
         * commands in the wrong order, meaning that the precondition of the
         * next command is NOT the postcondition of the current.
         *)
         List.fold
            (fun (pre, axiomsR) vcom ->
                 let cmd = vcom.Command
                 let post = vcom.Post
                 (post, trial {// If our last axiomatisation failed, this will
                               // cause failure here.
                               let! axioms = axiomsR
                               let! cpair = makeAxiomConditionPair model pre post
                               let! axiom = modelAxiomOnCommand model cpair cmd
                               return axiom :: axioms } ))
            (block.Pre, ok [])
            block.Contents

    (* At the end of the above, we either have a list of axioms or an
     * error.  If we have the former, surround the axioms with the condition
     * pair derived from the precondition and postcondition of the block.
     *)
    trial {let! xs = axioms
           let! cpair = makeAxiomConditionPair model block.Pre bpost
           return {Conditions = cpair
                   Inner = List.rev xs}}

/// Converts a method to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
let modelAxiomsOnMethod model meth =
    // TODO(CaptainHayashi): method parameters
    modelAxiomsOnBlock model meth.Body
    |> lift (fun c -> c.Inner)

/// Converts a list of methods to a list of partially resolved axioms.
/// The list is enclosed in a Chessie result.
let modelAxioms model methods =
    // TODO(CaptainHayashi): method parameters
    List.map (modelAxiomsOnMethod model) methods
    |> collect
    |> lift List.concat

/// Checks a view prototype to see if it contains duplicate parameters.
let checkViewProtoDuplicates proto =
    let names = List.map snd proto.VPPars
    match (findDuplicates names) with
    | [] -> ok proto
    | ds -> List.map (fun d -> VPEDuplicateParam (proto, d)) ds |> Bad

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
    trial {let! vprotos = modelViewProtos collated.CVProtos |> mapMessages MEVProto 
           // Make variable maps out of the global and local variable definitions.
           let! globals = makeVarMap ctx collated.CGlobals
                          |> mapMessages MEVar
           let! locals = makeVarMap ctx collated.CLocals
                         |> mapMessages MEVar

           (* We use a 'partial' model, with no defining views or
            * axioms, in the creation of the constraints.
            *)
           let imod = {Context = ctx
                       Globals = globals
                       Locals = locals
                       VProtos = vprotos
                       DefViews = ()
                       Axioms = () }

           let! constraints = modelConstraints imod collated
                              |> mapMessages MEConstraint

           (* Now add in the constraints.  This is a different type from
            * imod, so it isn't convenient to use mutation or
            * {imod with...}.  For now, we create an entirely new model.
            *)
           let pmod = {Context = ctx
                       Globals = globals
                       Locals = locals
                       VProtos = vprotos
                       DefViews = constraints
                       Axioms = () }
           let! axioms = modelAxioms pmod collated.CMethods
                         |>mapMessages MEAxiom

           return (withAxioms axioms pmod) }

/// Converts a collated script to a model.
let model = modelWith (new Context ())
