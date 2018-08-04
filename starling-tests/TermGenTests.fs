/// <summary>
///     Tests for <c>TermGen</c>.
/// </summary>
module Starling.Tests.TermGen

open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.TermGen

open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.Symbolic
open Starling.Core.Var

module TestNormalise =

    [<Test>]
    let ``normalise converts 3 instances of A(x)[4] to A(x)[12]`` () =
        assertEqual
            (iterated
                (gfunc BTrue "A" [ normalBoolExpr (sbBefore "x") ] )
                (IInt 12L : IntExpr<Sym<MarkedVar>>))
            (normalise
                (iterated
                    (gfunc BTrue "A" [ normalBoolExpr (sbBefore "x") ] )
                    (IInt 4L : IntExpr<Sym<MarkedVar>>))
                3)


    [<Test>]
    let ``normalise converts 6 instances of A(x)[n] to A(x)[6*n]`` () =
        assertEqual
            (iterated
                (gfunc BTrue "A" [ normalBoolExpr (sbBefore "x") ] )
                (IMul [ siBefore "n"; IInt 6L ]))
            (normalise
                (iterated
                    (gfunc BTrue "A" [ normalBoolExpr (sbBefore "x") ] )
                    (siBefore "n"))
                6)

    [<Test>]
    let ``normalise converts 1 instances of A(x)[n] to A(x)[n]`` () =
        assertEqual
            (iterated
                (gfunc BTrue "A" [ normalBoolExpr (sbBefore "x") ] )
                (siBefore "n"))
            (normalise
                (iterated
                    (gfunc BTrue "A" [ normalBoolExpr (sbBefore "x") ] )
                    (siBefore "n"))
                1)


module TestWPreCreation =
    open Starling.Collections

    [<Test>]
    let ``Subtracting different funcs yields the original func`` () =
        assertEqual
            (Multiset.singleton <|
                iterated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 1L))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 1L) ]
                (Multiset.repeated
                    (gfunc BTrue "blop" [ normalBoolExpr (sbGoal 0I "bar") ])
                    11))

    [<Test>]
    let ``Subtracting emp from a single func yields the original func`` () =
        assertEqual
            (Multiset.singleton <|
                iterated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 1L))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 1L) ]
                Multiset.empty)

    [<Test>]
    let ``Subtracting a single func from emp yields emp`` () =
        assertEqual
            Multiset.empty
            (termGenWPreMinus
                []
                (Multiset.singleton
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])))

    [<Test>]
    let ``Subtracting emp from an iterated func yields the original func`` () =
        assertEqual
            (Multiset.singleton <|
                iterated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 10L))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 10L) ]
                Multiset.empty)

    [<Test>]
    let ``Exact-subtracting an iterated func from itself cancels out`` () =
        assertEqual
            Multiset.empty
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 9L) ]
                (Multiset.repeated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    9))

    [<Test>]
    let ``Over-subtracting an iterated func from itself truncates`` () =
        assertEqual
            Multiset.empty
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 10L) ]
                (Multiset.repeated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    11))

    [<Test>]
    let ``Under-subtracting an iterated func from itself leaves a remainder`` () =
        assertEqual
            (Multiset.singleton <|
                iterated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 4L))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 10L) ]
                (Multiset.repeated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    6))

    [<Test>]
    let ``Subtraction normalises the subtracted view correctly`` () =
        assertEqual
            (Multiset.singleton <|
                iterated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 2L))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 5L)
                  iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 3L) ]
                (Multiset.repeated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    6))

    [<Test>]
    let ``Subtraction normalises the subtracting view correctly`` () =
        assertEqual
            (Multiset.singleton <|
                iterated
                    (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 2L))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 10L) ]
                (Multiset.append
                    (Multiset.repeated
                        (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                        5)
                    (Multiset.repeated
                        (gfunc BTrue "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                        3)))


    [<Test>]
    let ``Subtracting a func from one with the same name generates an x!=y guard`` () =
        assertEqual
            (Multiset.singleton
                (iterated
                    (gfunc
                        (BNot (bEq (sbGoal 0I "bar")
                                    (sbAfter "baz")))
                        "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 1L)))
            (termGenWPreMinus
                [ iterated
                    (regFunc "foo" [ normalBoolExpr (sbGoal 0I "bar") ])
                    (IInt 1L) ]
                (Multiset.singleton
                    (gfunc BTrue "foo" [ normalBoolExpr (sbAfter "baz") ])))

    [<Test>]
    let ``General-case subtraction on one func produces the correct rewrite`` () =
        assertEqual
            (Multiset.ofFlatList
                [ (iterated
                    (gfunc
                        (mkNot
                            (mkAnd
                                [ sbBefore "G"
                                  bEq (sbAfter "x") (sbAfter "y") ]))
                        "A" [ normalBoolExpr (sbAfter "x") ])
                    (siAfter "n"))
                  (iterated
                    (gfunc
                        (BAnd
                            [ sbBefore "G"
                              bEq (sbAfter "x") (sbAfter "y")
                              mkIntGt (siAfter "n") (IInt 1L) ])
                        "A" [ normalBoolExpr (sbAfter "x") ])
                    (mkDec (siAfter "n"))) ])
            (termGenWPreMinus
                [ iterated
                    (regFunc "A" [ normalBoolExpr (sbAfter "x") ])
                    (siAfter "n") ]
                (Multiset.singleton
                    (gfunc (sbBefore "G") "A" [ normalBoolExpr (sbAfter "y") ])))