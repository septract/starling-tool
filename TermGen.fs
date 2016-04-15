/// The part of Starling that generates unreified terms from framed
/// axioms.
module Starling.TermGen

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
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
    let ql = Multiset.toFlatList q

    ql
    |> List.fold termGenFrameView (List.map guard r)
    |> Multiset.ofFlatList

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
    let post =
        gax.Axiom.Post
        |> subExprInGView (liftMarker After always)
    let goal = gax.Goal

    Multiset.append pre (termGenFrame goal post)

/// Generates a term from a goal axiom.
let termGenAxiom gax =
    { WPre = termGenPre gax
      Goal = gax.Goal
      Cmd = gax.Axiom.Cmd }

/// Converts a model's goal axioms to terms.
let termGen : UVModel<GoalAxiom> -> UVModel<PTerm<GView, OView>> =
    mapAxioms termGenAxiom


/// <summary>
///     Tests for <c>TermGen</c>.
/// </summary>
module Tests =
    open NUnit.Framework


    let tcd : obj[] -> TestCaseData = TestCaseData

    /// <summary>
    ///     NUnit tests for <c>TermGen</c>.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for <c>termGenFrame</c>.
        /// </summary>
        static member FrameSubtracts =
            [ (tcd [| (List.singleton <|
                           func "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                      (Multiset.empty : GView) |] )
                  .Returns(Multiset.singleton <|
                           gfunc BTrue "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                  .SetName("Removing emp from a func yields the original func")
              (tcd [| (List.singleton <|
                           func "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                      (Multiset.singleton <|
                           gfunc BTrue "foo" [ Expr.Bool (bAfter "baz") ] ) |] )
                  .Returns(Multiset.singleton <|
                           gfunc (BNot (bEq (bGoal 0I "bar")
                                            (bAfter "baz")))
                                "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                  .SetName("Removing a func from itself generates a !x=y-guarded view")
              (tcd [| (List.singleton <|
                           func "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                      (Multiset.singleton <|
                           gfunc BTrue "blop" [ Expr.Bool (bAfter "baz") ] ) |] )
                  .Returns(Multiset.singleton <|
                           gfunc BTrue "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                  .SetName("Removing a func from itself is inert")
              (tcd [| (Multiset.ofFlatList>>Multiset.toFlatList 
                       <|
                           [ func "foo" [ Expr.Bool (bGoal 0I "bar") ]
                             func "foo" [ Expr.Bool (bGoal 1I "bar") ] ] )
                      (Multiset.singleton <|
                           gfunc BTrue "foo" [ Expr.Bool (bAfter "baz") ] ) |] )
                  .Returns(Multiset.ofFlatList <|
                           [ gfunc (BNot (bEq (bGoal 0I "bar")
                                              (bAfter "baz")))
                                   "foo" [ Expr.Bool (bGoal 0I "bar") ]
                             gfunc (mkNot
                                        (mkAnd
                                             [ (mkNot (bEq (bGoal 0I "bar")
                                                           (bAfter "baz")))
                                               (bEq (bGoal 1I "bar")
                                                    (bAfter "baz")) ] ))
                                   "foo" [ Typed.Bool (bGoal 1I "bar") ]] )
                  .SetName("Removing a func from two copies of itself works correctly")
              (tcd [| (List.singleton <|
                           func "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                      (Multiset.singleton <|
                           gfunc (BGt (aAfter "x",
                                       aAfter "y"))
                                 "foo" [ Expr.Bool (bAfter "baz") ] ) |] )
                  .Returns(Multiset.singleton <|
                           gfunc (mkNot (BAnd [ (BGt (aAfter "x",
                                                      aAfter "y"))
                                                (bEq (bGoal 0I "bar")
                                                     (bAfter "baz")) ] ))
                                 "foo" [ Expr.Bool (bGoal 0I "bar") ] )
                  .SetName("Removing a guarded func from itself works correctly")
              (tcd [| (List.empty : OView)
                      (Multiset.singleton <|
                           gfunc BTrue "foo" [ Expr.Bool (bBefore "bar") ] ) |] )
                  .Returns(Multiset.empty : GView)
                  .SetName("Removing a func from emp yields emp") ]

        /// <summary>
        ///     Tests <c>termGenFrame</c>.
        /// </summary>
        [<TestCaseSource("FrameSubtracts")>]
        member x.``termGenFrame performs multiset minus correctly`` r q =
            termGenFrame r q
