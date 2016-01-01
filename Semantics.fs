/// Module containing the semantic definitions of commands.
module Starling.Semantics

open Microsoft.Z3
open Chessie.ErrorHandling
open Starling.Collections
open Starling.Z3
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Lang.Modeller

//
// Atomic emitters
//

/// Makes the relation after!after = before!before.
let makeRel model before after = 
    let beforeB = subAllInModel model envVarToBefore before
    let afterA = subAllInModel model envVarToAfter after
    mkEq model.Context afterA beforeB

/// Given e, returns e!after = e!before.
let makeNoChange model expr = 
    let exprA = subAllInModel model envVarToAfter expr
    let exprB = subAllInModel model envVarToBefore expr
    mkEq model.Context exprA exprB

/// Given some ArithExpr over a lvalue, return the relation for the
/// operation identified by the given fetch mode on that lvalue.
let makeFetchUpdate model (expr : ArithExpr) mode = 
    let ctx = model.Context
    let exprB = (subAllInModel model envVarToBefore (expr :> Expr)) :?> ArithExpr
    let exprA = (subAllInModel model envVarToAfter (expr :> Expr)) :?> ArithExpr
    
    let exprMod = 
        match mode with
        // 'expr' -> expr!after = expr!before.
        | Direct -> exprB
        // 'expr++' -> expr!after = expr!before + 1.
        | Increment -> mkAdd2 ctx exprB (mkAInt ctx 1)
        // 'expr--' -> expr!after = expr!before - 1.
        | Decrement -> mkSub2 ctx exprB (mkAInt ctx 1)
    mkEq ctx exprA exprMod

/// Emits Z3 corresponding to a compare-and-swap.
let makeCAS model destE testE setE = 
    let ctx = model.Context
    (* Compare-and-swap gets its semantics in two steps:
     * 1) Success--dest becomes set; test held.
     * 2) Failure--test becomes dest; dest held.
     * In both cases, set is not modified.
     *)

    // Make the before-case versions of dest and test.
    let destEB = (subAllInModel model envVarToBefore destE)
    let testEB = (subAllInModel model envVarToBefore testE)
    let setEB = (subAllInModel model envVarToBefore setE)
    (* Now we make the cases.
     * Each case is in the form (cond => destAfter ^ testAfter).
     * We start with the success case.
     *)
    let succCond = mkEq ctx destEB testEB
    // In a success, we have destE!after = setE!before;
    let succDest = makeRel model setE destE
    // and test!after = test!before.
    let succTest = makeNoChange model testE
    let succSem = mkAnd2 ctx succDest succTest
    let success = mkImplies ctx succCond succSem
    let failCond = mkNot ctx succCond
    // In a failure, we have testE!after = destE!before;
    let failDest = makeRel model destE testE
    // and dest!after = dest!before.
    let failTest = makeNoChange model destE
    let failSem = mkAnd2 ctx failDest failTest
    let failure = mkImplies ctx failCond failSem
    [ success
      failure
      // This models set!after = set!before.
      makeNoChange model setE ]

/// Emits an arithmetic fetch.
let makeIntLoad model dest src mode = 
    let ctx = model.Context
    (* Convert the lvalues to constants.
     * Note that a destination is optional.
     *)
    let destE = Option.map (mkIntLV ctx) dest
    let srcE = mkIntLV ctx src
    [ (* We have to use Some and List.collect to ensure that the term
       * for dest is only included if there actually _is_ a dest.
       *)
      // If dest exists, create dest!after = src!before.
      Option.map (makeRel model srcE) destE
      // Create src!after = F(src!before), where F is
      // defined by the fetch mode.
      makeFetchUpdate model srcE mode |> Some ]
    |> List.choose id

/// Emits a Boolean fetch.
let makeBoolLoad model dest src = 
    let ctx = model.Context
    (* As above, but with different types, no modes other than
     * Direct, and a mandatory dest.
     *)
    let destE = mkBoolLV ctx dest
    let srcE = mkBoolLV ctx src
    [ makeRel model srcE destE
      makeNoChange model srcE ]

/// Emits an integral store.
let makeIntStore model dest srcE = 
    let ctx = model.Context
    // We don't emit a makeNoChange for src, because src is an expression.
    let destE = mkIntLV ctx dest
    [ makeRel model srcE destE ]

/// Emits a Boolean store.
let makeBoolStore model dest srcE = 
    let ctx = model.Context
    let destE = mkBoolLV ctx dest
    [ makeRel model srcE destE ]

/// Emits Z3 corresponding to a prim.
/// The result is a pair of the Z3 emission, and the set of names of
/// variables whose post-states are bound by the semantics.
let emitPrim model prim = 
    let ctx = model.Context
    match prim with
    | IntLoad(dest, src, mode) -> makeIntLoad model dest src mode
    | BoolLoad(dest, src) -> makeBoolLoad model dest src
    | IntStore(dest, src) -> makeIntStore model dest src
    | BoolStore(dest, src) -> makeBoolStore model dest src
    | IntCAS(dest, test, set) -> makeCAS model (mkIntLV ctx dest :> Expr) (mkIntLV ctx test :> Expr) set
    | BoolCAS(dest, test, set) -> makeCAS model (mkBoolLV ctx dest :> Expr) (mkBoolLV ctx test :> Expr) set
    | IntLocalSet(dest, srcE) -> 
        (* By the meta-theory, this and BoolLocalSet can be modelled
         * similarly to atomic fetches.
         * However, src is an expression, and (currently) cannot modify
         * dest, so we don't hold it invariant here.
         *)
        let ctx = model.Context
        let destE = mkIntLV ctx dest
        [ makeRel model srcE destE ]
    | BoolLocalSet(dest, srcE) -> 
        let ctx = model.Context
        let destE = mkBoolLV ctx dest
        [ makeRel model srcE destE ]
    | PrimId -> [ ctx.MkTrue() ]
    | PrimAssume(assumption) -> [ // Assumes always only refer to the pre-state.
                                  subAllInModel model envVarToBefore (assumption :> Expr) :?> BoolExpr ]

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame model expr = 
    let afts = aftersNotInExpr model expr
    let vars = Seq.append (Map.toSeq model.Globals) (Map.toSeq model.Locals)
    // TODO(CaptainHayashi): this is fairly inefficient.
    vars
    |> Seq.map (snd >> eraseVar)
    // ^ Get a sequence of all untyped variable records...
    |> Seq.filter (fun v -> Set.contains v.VarPostExpr afts)
    // ^ ... then find the ones that are not bound after the expr...
    |> Seq.map (fun v -> makeNoChange model v.VarExpr)

// ^ ... then prepare v!after = v!before records for them.
/// Translate a Prim to an expression completely characterising it.
/// This is the combination of the Prim's action (via emitPrim) and
/// a set of framing terms forcing unbound variables to remain constant
/// (through frame).
let semanticsOf model prim = 
    let ctx = model.Context
    let actions = emitPrim model prim
    // Temporarily build an And so we can check it with frame.
    // TODO(CaptainHayashi): eliminate this round-trip?
    let actionsAnd = actions |> List.toArray
    let aframe = frame model (mkAnd ctx actionsAnd)
    actions
    |> Seq.ofList
    |> Seq.append aframe
    |> mkAnd ctx

/// Substitutes all of the variables in a View using the given
/// substitution.
let subView sub model v = { v with VParams = List.map (subAllInModel model sub) v.VParams }

/// Substitutes all of the variables in a GuarView using the given substitution.
let subGuarView sub model gv = 
    { GCond = subAllInModel model sub (gv.GCond :> Expr) :?> BoolExpr
      GItem = subView sub model gv.GItem }

/// Substitutes all of the variables in a condition using the given substitution.
/// In this case, a condition is a list of GuarViews.
let subCondition sub model = Multiset.map (subGuarView sub model)

/// Renames the variables in a condition to before/after states.
let renameCondition model cond = 
    { (* Preconditions are in terms of global befores and local befores.
       * Postconditions are in terms of global befores, but local _afters_.
       *
       * Since we don't see any global values until we reify, and we've
       * already checked during modelling that we don't have any, we can
       * just perform a full substitution using the substitution rule for
       * locals.
       *)
      Pre = subCondition envVarToBefore model cond.Pre
      Post = subCondition envVarToAfter model cond.Post }

/// Translates a model axiom into an axiom over a semantic expression.
let translateAxiom model axiom = 
    { Conditions = renameCondition model axiom.Conditions
      Inner = semanticsOf model axiom.Inner }

/// Translate a model's axioms to axioms over semantic expressions.
let translateAxioms model = List.map (translateAxiom model) model.Axioms

/// Translate a model over Prims to a model over semantic expressions.
let translate model = withAxioms (translateAxioms model) model
