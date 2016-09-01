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

/// <summary>
///     Type of variables in funcs and views handled by TermGen.
/// </summary>
type TermGenVar = Sym<MarkedVar>

/// <summary>
///     Normalises the iterator of an iterated func stored multiple times in a
///     view.
///     <para>
///         This converts <paramref name="i"/> copies of
///         <c>V(x)[n]</c> into one copy of <c>V(x)[n*i]</c>.
///     </para>
/// </summary>
/// <param name="func">
///     The <see cref="IteratedGFunc"/> to normalise.
/// </param>
/// <param name="i">
///     The number of times <paramref name="func"/> appears in its view.
/// </param>
/// <returns>
///     The normalised version of <paramref name="func"/> with respect to
///     <paramref name="i"/>.
/// </returns>
let normalise (func : IteratedGFunc<TermGenVar>) (i : int)
  : IteratedGFunc<TermGenVar> =
    // TODO(CaptainHayashi): simplify multiplication if 1 or 0.
    mapIterator (mkMul2 (AInt (int64 i))) func

/// <summary>
///     Performs view minus of a view by a single func.
/// </summary>
/// <param name="qstep">
///     The func to subtract.
/// </param>
/// <param name="r">
///     The view to be subtracted from.
/// </param>
/// <param name="rdone">
///     A view to be merged with <paramref name="r"/> on termination.  This
///     usually carries the result of previous view minusing on a view of which
///     <paramref name="r"/> and <paramref name="rdone"/> are both part.
/// </param>
/// <returns>
///     The result of performing the view minus, merged with
///     <paramref name="rdone"/>.
/// </returns>
let rec minusViewByFunc (qstep : IteratedGFunc<TermGenVar>)
  (r : IteratedGView<TermGenVar>)
  (rdone : IteratedGView<TermGenVar>)
  : IteratedGView<TermGenVar> =
    // Let qstep = (g2 -> w(ybar)^k).
    let { Func = { Cond = g2; Item = { Name = w; Params = ybar } }
          Iterator = ko } = qstep
    let k = withDefault (AInt 1L) ko

    // If g2 is never true, then _nothing_ in r can ever be minused by it.
    if isFalse g2 then Multiset.append r rdone
    else
        // Base case: r is emp; inductive case: r is rstep+rnext.
        match Multiset.pop r with
        | None -> rdone
        | Some (rstepU, rnext, i) ->
            // Turn i copies of rstepU into a single func.
            let rstep = normalise rstepU i

            // Let rstep = (g1 -> v(xbar)^n),
            let { Func = { Cond = g1; Item = { Name = v; Params = xbar } }
                  Iterator = no } = rstep
            let n = withDefault (AInt 1L) no

            (* If v <> w, then the two funcs are disjoint, minusing does
               nothing, and we continue to the next element in r with no
               modification to rstep or qstep. *)
            if v <> w
            then minusViewByFunc qstep rnext (Multiset.add rdone rstep)
            (* If g1 is trivially false, then rstep simplifies to emp,
               cannot be minused, and we continue as if rstep never existed. *)
            else if isFalse g1 then minusViewByFunc qstep rnext rdone
            else
                (* Otherwise, we apply the rewrite rule from the meta-theory:

                   ((g1 -> v(xbar)^n) * rnext) \ (g2 -> v(ybar)^k)
                   =   (g1 ^ g2 ^ xbar=ybar ^ n>k -> v(xbar)^n-k)       =rsucc
                     * (g1 ^ !(g2 ^ xbar=ybar)    -> v(xbar)^n)         =rfail
                     * ((rnext
                         \ (g2 ^ g1 ^ xbar=ybar ^ k>n -> v(ybar)^k-n))  =qsucc
                        \  (g2 ^ !(g1 ^ xbar=ybar)    -> v(ybar)^k)))   =qfail

                   Our first task is to decide what each guarded func
                   (rsucc, rfail, qsucc, qfail) is. *)

                let barEq = List.map2 mkEq xbar ybar |> mkAnd

                let rSuccG = mkAnd [ g1; g2; barEq; mkGt n k ]
                let rSucc =
                    { Func = { Cond = rSuccG; Item = func v xbar };
                      Iterator = Some <| mkSub2 n k }
                let rFailG = mkAnd [ g1; mkNot (mkAnd2 g2 barEq) ]
                let rFail =
                    { Func = { Cond = rFailG; Item = func v xbar }
                      Iterator = Some n }
                let qSuccG = mkAnd [ g2; g1; barEq; mkGt k n ]
                let qSucc =
                    { Func = { Cond = qSuccG; Item = func v ybar }
                      Iterator = Some <| mkSub2 k n }
                let qFailG = mkAnd [ g2; mkNot (mkAnd2 g1 barEq) ]
                let qFail =
                    { Func = { Cond = qFailG; Item = func v ybar }
                      Iterator = Some k }

                (* Now, we have to minus qSucc and qFail from rnext.  The first
                   one is done in isolation (because eg. if we added rdone we'd
                   accidentally calculate rdone/qFail!), but we can optimise the
                   second one by passing through all the already-minused bits of
                   (rdone, rSucc, rFail) as the new rdone. *)

                // No need to check whether qSuccG/qFailG are trivially false:
                // it's the first thing we'll do in each recursive call.
                let innerMinus = minusViewByFunc qSucc rnext Multiset.empty
                minusViewByFunc
                    qFail
                    innerMinus
                    (Multiset.add (Multiset.add rdone rSucc) rFail)

/// <summary>
///     Generates the frame part of the weakest precondition.
///     <para>
///         In the meta-theory, this is <c>R \ Q</c>.
///     </para>
/// </summary>
/// <param name="r">
///     The view representing the goal to be subtracted from.
/// </param>
/// <param name="q">
///     The view representing the postcondition to subtract.
/// </param>
/// <returns>
///     The subtracted frame view.
/// </returns>
let termGenFrame
  (r : OView)
  (q : IteratedGView<Sym<MarkedVar>>)
  : IteratedGView<Sym<MarkedVar>> =
    (* Since R is unguarded and ordered at the start of the minus, we lift
       it to the guarded unordered view (forall f in R, (true -> Rn)). *)
    let rGuard =
        r
        |> List.map (mapIterated (fun f -> { Cond = BTrue; Item = f }))
        |> Multiset.ofFlatList

    (* We need to reduce the full multiset minus R \ Q
       into the easier minus ((G1 -> V1^n) * B) \ (G2 -> V2^k).  Part of
       this is done by minusViewByFunc, giving us the obligation to turn
       Q into a series of calls over a single func.  Thankfully, we have
       the law
         R \ (Qstep * Qrest) = (R \ Qstep) \ Qrest
       which turns our job into a simple fold over Q. *)
    Multiset.fold
        (fun rSoFar qStep i ->
             minusViewByFunc (normalise qStep i) rSoFar Multiset.empty)
        rGuard
        q

/// Generates a (weakest) precondition from a framed axiom.
let termGenPre
  (gax : GoalAxiom<'cmd>)
  : IteratedGView<Sym<MarkedVar>> =
    (* Theoretically speaking, this is crunching an axiom {P} C {Q} and
     * goal view R into (P * (R \ Q)), where R \ Q is the weakest frame.
     * Remember that * is multiset append.
     * \ is trickier because we have guarded axioms, and is thus left
     * to termGenSeptract.
     *
     * At this stage, we also rename all constants in pre to their pre-state,
     * and those in post to their post-state.  This is sound because, at this
     * stage, both sides only contain local variables.
     *)
    let _, pre = subExprInIteratedGView before NoCtx gax.Axiom.Pre
    let _, post = subExprInIteratedGView after NoCtx gax.Axiom.Post
    let goal = gax.Goal

    Multiset.append pre (termGenFrame goal post)

/// Generates a term from a goal axiom.
let termGenAxiom (gax : GoalAxiom<'cmd>)
  : Term<'cmd, IteratedGView<Sym<MarkedVar>>, OView> =
    { WPre = termGenPre gax
      Goal = gax.Goal
      Cmd = gax.Axiom.Cmd }

/// Converts a model's goal axioms to terms.
let termGen (model : Model<GoalAxiom<'cmd>, _>)
  : Model<Term<'cmd, IteratedGView<Sym<MarkedVar>>, OView>, _> =
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
                      (Multiset.empty : GView<Sym<MarkedVar>>) |] )
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
              (tcd [| ([] : OView)
                      (Multiset.singleton <|
                           smgfunc BTrue "foo" [ Expr.Bool (sbBefore "bar") ] ) |] )
                  .Returns(Multiset.empty : GView<Sym<MarkedVar>>)
                  .SetName("Removing a func from emp yields emp") ]

        /// <summary>
        ///     Tests <c>termGenFrame</c>.
        /// </summary>
        [<TestCaseSource("FrameSubtracts")>]
        member x.``termGenFrame performs multiset minus correctly`` r q =
            termGenFrame r q
