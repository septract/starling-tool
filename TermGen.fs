/// <summary>
///     The part of Starling that generates unreified terms from framed
///     axioms.
/// </summary>
module Starling.TermGen

open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.View.Sub
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Sub
open Starling.Core.Sub
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Axiom
open Starling.Core.Var


/// Performs one step of a multiset minus of a GView.
let termGenFrameStep : GFunc<'a> list * GFunc<'a> -> GFunc<'a> -> GFunc<'a> list * GFunc<'a> =
    fun (rdone, qstep) rnext ->
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
let termGenFrame : OView -> SMGView -> Multiset<GFunc<Sym<MarkedVar>>> =
    fun r q ->
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
let termGenPre
  (gax : GoalAxiom<'cmd>)
  : SMGView =
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
    let _, pre = subExprInGView before NoCtx gax.Axiom.Pre
    let _, post = subExprInGView after NoCtx gax.Axiom.Post
    let goal = gax.Goal

    Multiset.append pre (termGenFrame goal post)

/// Generates a term from a goal axiom.
let termGenAxiom (gax : GoalAxiom<'cmd>)
  : Term<'cmd, SMGView, OView> =
    { WPre = termGenPre gax
      Goal = gax.Goal
      Cmd = gax.Axiom.Cmd }

/// Converts a model's goal axioms to terms.
let termGen (model : Model<GoalAxiom<'cmd>, _>)
  : Model<Term<'cmd, SMGView, OView>, _> =
    mapAxioms termGenAxiom model


/// <summary>
///     Tests for <c>TermGen</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Starling.Utils.Testing


    /// <summary>
    ///     NUnit tests for <c>TermGen</c>.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for <c>termGenFrame</c>.
        /// </summary>
        static member FrameSubtracts =
            [ (tcd [| (List.singleton <|
                           func "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                      (Multiset.empty : SMGView) |] )
                  .Returns(Multiset.singleton <|
                           smgfunc BTrue "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                  .SetName("Removing emp from a func yields the original func")
              (tcd [| (List.singleton <|
                           smvfunc "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                      (Multiset.singleton <|
                           smgfunc BTrue "foo" [ Expr.Bool (sbAfter "baz") ] ) |] )
                  .Returns(Multiset.singleton <|
                           smgfunc
                               (BNot (bEq (sbGoal 0I "bar")
                                          (sbAfter "baz")))
                               "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                  .SetName("Removing a func from itself generates a !x=y-guarded view")
              (tcd [| (List.singleton <|
                           smvfunc "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                      (Multiset.singleton <|
                           smgfunc BTrue "blop" [ Expr.Bool (sbAfter "baz") ] ) |] )
                  .Returns(Multiset.singleton <|
                           smgfunc BTrue "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                  .SetName("Removing a func from itself is inert")
              (tcd [| (Multiset.ofFlatList>>Multiset.toFlatList
                       <|
                           [ smvfunc "foo" [ Expr.Bool (sbGoal 0I "bar") ]
                             smvfunc "foo" [ Expr.Bool (sbGoal 1I "bar") ] ] )
                      (Multiset.singleton <|
                           smgfunc BTrue "foo" [ Expr.Bool (sbAfter "baz") ] ) |] )
                  .Returns(Multiset.ofFlatList <|
                           [ smgfunc
                                 (BNot (bEq (sbGoal 0I "bar")
                                            (sbAfter "baz")))
                                 "foo"
                                 [ Expr.Bool (sbGoal 0I "bar") ]
                             smgfunc
                                 (mkNot
                                      (mkAnd
                                           [ (mkNot (bEq (sbGoal 0I "bar")
                                                         (sbAfter "baz")))
                                             (bEq (sbGoal 1I "bar")
                                                  (sbAfter "baz")) ] ))
                                 "foo"
                                 [ Typed.Bool (sbGoal 1I "bar") ]] )
                  .SetName("Removing a func from two copies of itself works correctly")
              (tcd [| (List.singleton <|
                           smvfunc "foo" [ Expr.Bool (sbGoal 0I "bar") ] )
                      (Multiset.singleton <|
                           smgfunc
                               (BGt (siAfter "x",
                                     siAfter "y"))
                               "foo"
                               [ Expr.Bool (sbAfter "baz") ] ) |] )
                  .Returns(Multiset.singleton <|
                           smgfunc
                               (mkNot (BAnd [ (BGt (siAfter "x",
                                                    siAfter "y"))
                                              (bEq (sbGoal 0I "bar")
                                                   (sbAfter "baz")) ] ))
                               "foo"
                               [ Expr.Bool (sbGoal 0I "bar") ] )
                  .SetName("Removing a guarded func from itself works correctly")
              (tcd [| (List.empty : OView)
                      (Multiset.singleton <|
                           smgfunc BTrue "foo" [ Expr.Bool (sbBefore "bar") ] ) |] )
                  .Returns(Multiset.empty : SMGView)
                  .SetName("Removing a func from emp yields emp") ]

        /// <summary>
        ///     Tests <c>termGenFrame</c>.
        /// </summary>
        [<TestCaseSource("FrameSubtracts")>]
        member x.``termGenFrame performs multiset minus correctly`` r q =
            termGenFrame r q
