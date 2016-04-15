module Starling.Tests.Instantiate

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Instantiate


let none : Option<BoolExpr> = None

/// Tests for the func instantiation functions.
type InstantiateTests() =
    
    /// Environment of test funcs.
    static member TestFuncs =
        [ (dfunc "foo" [],
           aEq (AInt 5L) (AInt 6L))
          (dfunc "bar" [ Param.Int "quux" ],
           aEq (aUnmarked "quux") (aUnmarked "blob"))
          (dfunc "baz" [ Param.Int "quux" ; Param.Bool "flop" ],
           BAnd [bUnmarked "flop"; BGt (aUnmarked "quux", aUnmarked "quux")]) ]


    /// Test cases for testing valid instantiation.
    static member ValidInstantiations =
        [ TestCaseData(vfunc "nope" [])
            .Returns(none |> Some)
            .SetName("Instantiate undefined func")
          TestCaseData(vfunc "foo" [])
            .Returns(aEq (AInt 5L) (AInt 6L) |> Some |> Some)
            .SetName("Instantiate func with no arguments")
          TestCaseData(vfunc "bar" [AInt 101L |> Expr.Int])
            .Returns(aEq (AInt 101L) (aUnmarked "blob") |> Some |> Some)
            .SetName("Instantiate func with one int argument")
          TestCaseData(vfunc "baz" [aAfter "burble" |> Expr.Int ; BTrue |> Expr.Bool])
            .Returns(BAnd [BTrue; BGt (aAfter "burble", aAfter "burble")] |> Some |> Some)
            .SetName("Instantiate func with two arguments of different types") ]
          
    /// Tests whether valid instantiations work.
    [<TestCaseSource("ValidInstantiations")>]
    member x.``Valid instantiations are executed correctly`` func =
        instantiate func InstantiateTests.TestFuncs |> okOption


    /// Test cases for testing invalid instantiation.
    static member InvalidInstantiations =
        [ TestCaseData(vfunc "foo" [AInt 101L |> Expr.Int])
            .Returns([CountMismatch(1, 0)] |> Some)
            .SetName("Instantiate func with too many arguments")
          TestCaseData(vfunc "bar" [])
            .Returns([CountMismatch(0, 1)] |> Some)
            .SetName("Instantiate func with too few arguments")
          TestCaseData(vfunc "baz" [BTrue |> Expr.Bool ; aAfter "burble" |> Expr.Int])
            .Returns([TypeMismatch (Param.Int "quux", Type.Bool ())
                      TypeMismatch (Param.Bool "flop", Type.Int ())] |> Some)
            .SetName("Instantiate func with two arguments of incorrect types") ]
          
    /// Tests whether invalid instantiations (don't) work.
    [<TestCaseSource("InvalidInstantiations")>]
    member x.``Invalid instantiations raise correct errors`` func =
        instantiate func InstantiateTests.TestFuncs |> failOption
