/// The part of Starling that generates unreified terms from framed
/// axioms.
module Starling.TermGen

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.GuardedView
open Starling.Core.Sub
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Axiom


/// Performs one step of a multiset minus of a GView.
let termGenFrameStep (rdone, qstep) rnext =
    (* This is based on Matt Parkinson's schema:
     * [rdone * rnext@(B1, p xbar) * rrest] *- qstep@(B2, p xbar2)
     * = rdone2@[rdone * rnext2@(B1 && !(B2 && xbar = xbar2), p xbar)]
     *   * (rrest *- qstep2@(B2 && !(B1 && xbar = xbar2), p xbar2))
     *
     * We lift this over view names: if the view is different on both
     * sides, we instead have rdone2 = rdone * rnext, qstep2 = qstep
     *
     * Our return value is (rdone2, qstep2).
     *)
    let rname = rnext.Item.Name
    let qname = qstep.Item.Name
    if rname = qname then
        let b1 = rnext.Cond
        let b2 = qstep.Cond
        let xbar = rnext.Item.Params
        let xbar2 = qstep.Item.Params
        // xbar = xbar'
        let xbarEq = List.map2 mkEq xbar xbar2 |> mkAnd

        // B2 && !(B1 && xbar = xbar2)
        let qcond =
            mkAnd [ b2
                    mkNot (mkAnd [ b1; xbarEq ]) ]

        let qstep2 = { qstep with Cond = qcond }

        // B1 && !(B2 && xbar = xbar2)
        let rcond =
            mkAnd [ b1
                    mkNot (mkAnd [ b2; xbarEq ]) ]

        if isFalse rcond then
            (rdone, qstep2)
        else
            let rnext2 = { rnext with Cond = rcond }
            (rnext2 :: rdone, qstep2)
    else (rnext :: rdone, qstep)

/// Performs multiset minus of the single GView q from the GView
/// multiset r, returning r \ q.
let termGenFrameView r q = List.fold termGenFrameStep ([], q) r |> fst

/// Guards a goal view with true.
let guard r = { Cond = BTrue; Item = r }

/// Generates the frame part of the weakest precondition.
let termGenFrame r q =
    (* We iterate on multiset minus of each item in q:
     * A \ (B * C) = (A \ B) \ C
     *
     * Since r is unguarded at the start of the minus, we lift it
     * to the guarded view (true|r).
     *)
    List.fold termGenFrameView (List.map guard r) q

/// Generates a (weakest) precondition from a framed axiom.
let termGenPre gax =
    (* Theoretically speaking, this is crunching an axiom {P} C {Q} and
     * goal view R into (P * (R \ Q)), where R \ Q is the weakest frame.
     * Remember that * is multiset union.
     * \ is trickier because we have guarded axioms, and is thus left
     * to termGenSeptract.
     *
     * At this stage, we also rename all constants in pre to their pre-state,
     * and those in post to their post-state.  This is sound because, at this
     * stage, both sides only contain local variables.
     *)
    // TODO(CaptainHayashi): use something better than lists.
    let pre =
        gax.Axiom.Pre
        |> subExprInGView (liftMarker Before always)
        |> Multiset.toFlatList
    let post =
        gax.Axiom.Post
        |> subExprInGView (liftMarker After always)
        |> Multiset.toFlatList
    let goal = gax.Goal |> Multiset.toFlatList
    List.append pre (termGenFrame goal post) |> Multiset.ofFlatList

/// Generates a term from a goal axiom.
let termGenAxiom gax =
    { WPre = termGenPre gax
      Goal = gax.Goal
      Cmd = gax.Axiom.Cmd }

/// Converts a model's goal axioms to terms.
let termGen : Model<GoalAxiom, DView> -> Model<PTerm<GView, View>, DView> =
    mapAxioms termGenAxiom
