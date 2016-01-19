/// Tests for the reifier.
module Starling.Tests.Reifier

open NUnit.Framework
open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Reifier
open Starling.Tests.Studies

/// Tests for the reifier.
type ReifierTests() =

    /// Test cases for findDefOfView.
    static member FindDefOfViewCases =
        // TODO(CaptainHayashi): this isn't part of the reifier anymore...
        [   (
                new TestCaseData(
                    Multiset.ofList [ { Name = "holdLock"
                                        Params = [] }
                                      { Name = "holdTick"
                                        Params = [ AExpr (aUnmarked "t") ] } ]
                )
            ).Returns(
                Some(Multiset.ofList [ { Name = "holdLock"
                                         Params = [] }
                                       { Name = "holdTick"
                                         Params = [ (Type.Int, "t") ] } ])
            ).SetName("Find definition of view in the same order")
            (
                new TestCaseData(
                    Multiset.ofList [ { Name = "holdTick"
                                        Params = [ AExpr (aUnmarked "t") ] }
                                      { Name = "holdLock"
                                        Params = [] } ]
                )
            ).Returns(
                Some(Multiset.ofList [ { Name = "holdLock"
                                         Params = [] }
                                       { Name = "holdTick"
                                         Params = [ (Type.Int, "t") ] } ])
            ).SetName("Find definition of view in a reversed order")
        ]

    [<TestCaseSource("FindDefOfViewCases")>]
    /// Tests whether findDefOfView behaves correctly.
    member x.``findDefOfView finds view defs correctly on the ticketed lock`` view =
        view
        |> findDefOfView ticketLockModel.DefViews
        |> Option.map (fun x -> x.CViews)
