module Starling.Tests.Instantiate

open NUnit.Framework
open Starling.Collections
open Starling.Utils
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
           iEq (AInt 5L : MIntExpr) (AInt 6L))
          (dfunc "bar" [ Param.Int "quux" ],
           iEq (iUnmarked "quux") (iUnmarked "blob"))
          (dfunc "baz" [ Param.Int "quux" ; Param.Bool "flop" ],
           BAnd [bUnmarked "flop"; BGt (iUnmarked "quux", iUnmarked "quux")]) ]


    /// Test cases for testing valid instantiation.
    static member ValidInstantiations =
        [ TestCaseData(mvfunc "nope" [])
            .Returns(none |> Some)
            .SetName("Instantiate undefined func")
          TestCaseData(mvfunc "foo" [])
            .Returns(iEq (AInt 5L : MIntExpr) (AInt 6L : MIntExpr) |> Some |> Some)
            .SetName("Instantiate func with no arguments")
          TestCaseData(mvfunc "bar" [AInt 101L |> Expr.Int])
            .Returns(iEq (AInt 101L) (iUnmarked "blob") |> Some |> Some)
            .SetName("Instantiate func with one int argument")
          TestCaseData(mvfunc "baz" [iAfter "burble" |> Expr.Int ; BTrue |> Expr.Bool])
            .Returns(BAnd [BTrue; BGt (iAfter "burble", iAfter "burble")] |> Some |> Some)
            .SetName("Instantiate func with two arguments of different types") ]
          
    /// Tests whether valid instantiations work.
    [<TestCaseSource("ValidInstantiations")>]
    member x.``Valid instantiations are executed correctly`` func =
        func
        |> instantiate mvParamSubFun InstantiateTests.TestFuncs
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
            .Returns([TypeMismatch (Param.Int "quux", Type.Bool ())
                      TypeMismatch (Param.Bool "flop", Type.Int ())] |> Some)
            .SetName("Instantiate func with two arguments of incorrect types") ]
          
    /// Tests whether invalid instantiations (don't) work.
    [<TestCaseSource("InvalidInstantiations")>]
    member x.``Invalid instantiations raise correct errors`` func =
        func
        |> instantiate mvParamSubFun InstantiateTests.TestFuncs
        |> failOption
