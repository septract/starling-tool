/// <summary>
///     Collections used in Starling.
/// </summary>
module Starling.Tests.TermGen

open Starling.TermGen

open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.Symbolic
open Starling.Core.Var

/// <summary>
///     Tests for <c>TermGen</c>.
/// </summary>
module Tests =
    open NUnit.Framework

    module TestTermGen =
        module TestNormalise =

            [<Test>]
            let ``normalise converts 3 instances of A(x)[4] to A(x)[12]`` () =
                Assert.That(
                    normalise
                        (iterated
                            (gfunc BTrue "A" [ Bool (sbBefore "x") ] )
                            (Some (AInt 4L : IntExpr<Sym<MarkedVar>>)))
                        3,
                    Is.EqualTo(
                        (iterated
                            (gfunc BTrue "A" [ Bool (sbBefore "x") ] )
                            (Some (AInt 12L : IntExpr<Sym<MarkedVar>>)))))


            [<Test>]
            let ``normalise converts 6 instances of A(x)[n] to A(x)[6*n]`` () =
                Assert.That(
                    normalise
                        (iterated
                            (gfunc BTrue "A" [ Bool (sbBefore "x") ] )
                            (Some (siBefore "n")))
                        6,
                    Is.EqualTo(
                        (iterated
                            (gfunc BTrue "A" [ Bool (sbBefore "x") ] )
                            (Some (AMul [ siBefore "n"; AInt 6L ])))))


        module TestWPreCreation =
            [<Test>]
            let ``TODO Test MinusViewByFunc`` () =
                Assert.Fail ()

            [<Test>]
            let ``TODO Test TermGenPre`` () =
                Assert.Fail ()

    module TestIterFlatten =
        module TestLowerGuards =
            [<Test>]
            let ``Drop iterated GFunc down to non-iterated GFunc`` ()=
                Assert.AreEqual
                    ((iterated (gfunc BTrue "f" [Bool BTrue]) (Some (Int <| AInt 3L))),
                    (gfunc BTrue "f" [Int <| AInt 3L; Bool BTrue]))

            [<Test>]
            let ``Drop iterated SMVFunc down to non-iterated SMVFunc`` ()=
                Assert.AreEqual
                    ((iterated (smvfunc "f" [Bool BTrue]) (Some (Int <| AInt 3L))),
                    (smvfunc "f" [Int <| AInt 3L; Bool BTrue]))

            [<Test>]
            let ``Drop non-iterated IteratedSMVFunc's down to non-iterated SMVFunc`` ()=
                Assert.AreEqual
                    ((iterated (smvfunc "f" [Bool BTrue]) None),
                    (smvfunc "f" [Bool BTrue]))
(*
 *  old termgen test before iterated views were added
 *
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
              (tcd [| ([] : IteratedOView)
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
*)
