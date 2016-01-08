/// Module containing the semantic definitions of commands.
module Starling.Semantics

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Lang.Modeller

//
// Atomic emitters
//

/// Makes the generic relation after!after = before!before.
let makeRel before after = 
    // We mark all variables in each expression, hence always.
    mkEq (markVars After always after)
         (markVars Before always before)

/// Given some ArithExpr over a lvalue, return the relation for the
/// operation identified by the given fetch mode on that lvalue.
let makeFetchUpdate expr mode = 
    let exprB = arithMarkVars Before always expr
    let exprA = arithMarkVars After always expr
    
    let exprMod = 
        match mode with
        // 'expr' -> expr!after = expr!before.
        | Direct -> exprB
        // 'expr++' -> expr!after = expr!before + 1.
        | Increment -> mkAdd2 exprB (AInt 1L)
        // 'expr--' -> expr!after = expr!before - 1.
        | Decrement -> mkSub2 exprB (AInt 1L)
    mkEq (AExpr exprA) (AExpr exprMod)

/// Emits Z3 corresponding to a compare-and-swap.
let makeCAS destE testE setE = 
    (* Compare-and-swap gets its semantics in two steps:
     * 1) Success--dest becomes set; test held.
     * 2) Failure--test becomes dest; dest held.
     * In both cases, set is not modified.
     *)

    // Make the before-case versions of dest and test.
    let destEB = (markVars Before always destE)
    let testEB = (markVars Before always testE)
    let setEB = (markVars Before always setE)
    (* Now we make the cases.
     * Each case is in the form (cond => destAfter ^ testAfter).
     * We start with the success case.
     *)
    let succCond = mkEq destEB testEB
    // In a success, we have destE!after = setE!before;
    let succDest = makeRel setE destE
    // and test!after = test!before.
    let succTest = makeRel testE testE
    let succSem = mkAnd2 succDest succTest
    let success = mkImplies succCond succSem
    let failCond = mkNot succCond
    // In a failure, we have testE!after = destE!before;
    let failDest = makeRel destE testE
    // and dest!after = dest!before.
    let failTest = makeRel destE destE
    let failSem = mkAnd2 failDest failTest
    let failure = mkImplies failCond failSem
    [ success
      failure
      // This models set!after = set!before.
      makeRel setE setE ]

/// Emits an arithmetic fetch.
let makeIntLoad dest src mode = 
    (* Convert the lvalues to constants.
     * Note that a destination is optional.
     *)
    let destE = Option.map mkIntLV dest
    let srcE = mkIntLV src
    [ (* We have to use Some and List.collect to ensure that the term
       * for dest is only included if there actually _is_ a dest.
       *)
      // If dest exists, create dest!after = src!before.
      Option.map (AExpr >> makeRel (AExpr srcE)) destE
      // Create src!after = F(src!before), where F is
      // defined by the fetch mode.
      makeFetchUpdate srcE mode |> Some ]
    |> List.choose id

/// Emits a Boolean fetch.
let makeBoolLoad dest src = 
    (* As above, but with different types, no modes other than
     * Direct, and a mandatory dest.
     *)
    let destE = dest |> mkBoolLV |> BExpr
    let srcE = src |> mkBoolLV |> BExpr
    [ makeRel srcE destE
      makeRel srcE srcE ]

/// Emits an integral store.
let makeIntStore dest srcE = 
    // We don't emit a makeNoChange for src, because src is an expression.
    let destE = dest |> mkIntLV |> AExpr
    [ makeRel (AExpr srcE) destE ]

/// Emits a Boolean store.
let makeBoolStore dest srcE = 
    let destE = dest |> mkBoolLV |> BExpr
    [ makeRel (BExpr srcE) destE ]

/// Emits an Expr corresponding to a prim.
let emitPrim = 
    function
    | IntLoad(dest, src, mode) -> makeIntLoad dest src mode
    | BoolLoad(dest, src) -> makeBoolLoad dest src
    | IntStore(dest, src) -> makeIntStore dest src
    | BoolStore(dest, src) -> makeBoolStore dest src
    | IntCAS(dest, test, set) -> makeCAS (mkIntLV dest |> AExpr) (mkIntLV test |> AExpr) (set |> AExpr)
    | BoolCAS(dest, test, set) -> makeCAS (mkBoolLV dest |> BExpr) (mkBoolLV test |> BExpr) (set |> BExpr)
    | IntLocalSet(dest, srcE) -> 
        (* By the meta-theory, this and BoolLocalSet can be modelled
         * similarly to atomic fetches.
         * However, src is an expression, and (currently) cannot modify
         * dest, so we don't hold it invariant here.
         *)
        [ makeRel (srcE |> AExpr) (dest |> mkIntLV |> AExpr) ]
    | BoolLocalSet(dest, srcE) -> 
        [ makeRel (srcE |> BExpr) (dest |> mkBoolLV |> BExpr) ]
    | PrimId -> [ BTrue ]
    | PrimAssume(assumption) -> [ // Assumes always only refer to the pre-state.
                                  boolMarkVars Before always assumption ]

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame model expr = 
    // Find all the bound post-variables in the expression...
    let evars =
        expr
        |> varsInBool
        |> Seq.choose (function | After x -> Some x
                                | _ -> None)
        |> Set.ofSeq

    // Then, for all of the variables in the model, choose those not in evars, and make frame expressions for them.
    Seq.append (Map.toSeq model.Globals) (Map.toSeq model.Locals)
    // TODO(CaptainHayashi): this is fairly inefficient.
    |> Seq.filter (fun (name, ty) -> not (Set.contains name evars))
    |> Seq.map ((fun (name, ty) -> mkVarExp (ty, name)) >> (fun v -> makeRel v v))
    // ^ ... then prepare v!after = v!before records for them.

/// Translate a Prim to an expression completely characterising it.
/// This is the combination of the Prim's action (via emitPrim) and
/// a set of framing terms forcing unbound variables to remain constant
/// (through frame).
let semanticsOf model prim = 
    let actions = emitPrim prim
    // Temporarily build an And so we can check it with frame.
    // TODO(CaptainHayashi): eliminate this round-trip?
    let actionsAnd = actions |> List.toArray
    let aframe = frame model (mkAnd actionsAnd)
    actions
    |> Seq.ofList
    |> Seq.append aframe
    |> mkAnd 

/// Marks all of the variables in a View using the given  marker.
let markView marker vpred v = { v with Params = List.map (markVars marker vpred) v.Params }

/// Marks all of the variables in a GuarView using the given marker.
let markGuarView marker vpred {Cond = c; Item = i} = 
    { Cond = boolMarkVars marker vpred c
      Item = markView marker vpred i }

/// Marks all of the variables in a condition using the given marker.
/// In this case, a condition is a list of GuarViews.
let markCondition marker vpred = Multiset.map (markGuarView marker vpred)

/// Renames the variables in a condition to before/after states.
let renameCondition cond = 
    { (* Preconditions are in terms of global befores and local befores.
       * Postconditions are in terms of global befores, but local _afters_.
       *
       * Since we don't see any global values until we reify, and we've
       * already checked during modelling that we don't have any, we can
       * just perform a full substitution using the substitution rule for
       * locals.
       *)
      Pre = markCondition Before always cond.Pre
      Post = markCondition After always cond.Post }

/// Translates a model axiom into an axiom over a semantic expression.
let translateAxiom model axiom = 
    { Conditions = renameCondition axiom.Conditions
      Inner = semanticsOf model axiom.Inner }

/// Translate a model's axioms to axioms over semantic expressions.
let translateAxioms model = List.map (translateAxiom model) model.Axioms

/// Translate a model over Prims to a model over semantic expressions.
let translate model = withAxioms (translateAxioms model) model
