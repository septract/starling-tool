/// <summary>
///     Tests for <c>Starling.Core.Instantiate</c>.
/// </summary>
module Starling.Tests.Instantiate

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Instantiate


let none : Option<MBoolExpr> = None

/// Tests for the func instantiation functions.
type InstantiateTests() =

    /// Environment of test funcs.
    static member TestFuncs =
        [ (dfunc "foo" [],
           iEq (AInt 5L : VIntExpr) (AInt 6L))
          (dfunc "bar" [ Int "quux" ],
           iEq (AVar "quux") (AInt 6L))
          (dfunc "baz" [ Int "quux" ; Bool "flop" ],
           BAnd [BVar "flop"; BGt (AVar "quux", AVar "quux")]) ]


    /// Test cases for testing valid instantiation.
    static member ValidInstantiations =
        [ TestCaseData(mvfunc "nope" [])
            .Returns(none |> Some)
            .SetName("Instantiate undefined func")
          TestCaseData(mvfunc "foo" [])
            .Returns(iEq (AInt 5L : MIntExpr) (AInt 6L : MIntExpr) |> Some |> Some)
            .SetName("Instantiate func with no arguments")
          TestCaseData(mvfunc "bar" [AInt 101L |> Expr.Int])
            .Returns(iEq (AInt 101L) (AInt 6L : MIntExpr) |> Some |> Some)
            .SetName("Instantiate func with one int argument")
          TestCaseData(mvfunc "baz" [iAfter "burble" |> Expr.Int ; BTrue |> Expr.Bool])
            .Returns(BAnd [BTrue; BGt (iAfter "burble", iAfter "burble")] |> Some |> Some)
            .SetName("Instantiate func with two arguments of different types") ]

    /// Tests whether valid instantiations work.
    [<TestCaseSource("ValidInstantiations")>]
    member x.``Valid instantiations are executed correctly`` (func : MVFunc) =
        func
        |> instantiate paramSubFun InstantiateTests.TestFuncs
        |> okOption


    /// Test cases for testing invalid instantiation.
    static member InvalidInstantiations =
        [ TestCaseData(mvfunc "foo" [AInt 101L |> Expr.Int])
            .Returns([CountMismatch(1, 0)] |> Some)
            .SetName("Instantiate func with too many arguments")
          TestCaseData(mvfunc "bar" [])
            .Returns([CountMismatch(0, 1)] |> Some)
            .SetName("Instantiate func with too few arguments")
          TestCaseData(vfunc "baz" [BTrue |> Expr.Bool ; iAfter "burble" |> Expr.Int])
            .Returns([TypeMismatch (Int "quux", Bool ())
                      TypeMismatch (Bool "flop", Int ())] |> Some)
            .SetName("Instantiate func with two arguments of incorrect types") ]

    /// Tests whether invalid instantiations (don't) work.
    [<TestCaseSource("InvalidInstantiations")>]
    member x.``Invalid instantiations raise correct errors`` (func : MVFunc) =
        func
        |> instantiate paramSubFun InstantiateTests.TestFuncs
        |> failOption
