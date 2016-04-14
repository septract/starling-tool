/// Tests for the reifier.
module Starling.Tests.Reifier

open NUnit.Framework
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Reifier
open Starling.Tests.Studies

/// Tests for the reifier.
type ReifierTests() =

    /// Test cases for findDefOfView.
    static member FindDefOfViewCases =
        // TODO(CaptainHayashi): this isn't part of the reifier anymore...
        [   (
                new TestCaseData(
                    Multiset.ofFlatList
                        [ { Name = "holdLock"
                            Params = [] }
                          { Name = "holdTick"
                            Params = [ AExpr (aUnmarked "t") ] } ]
                )
            ).Returns(
                Some(Multiset.ofFlatList
                         [ { Name = "holdLock"
                             Params = [] }
                           { Name = "holdTick"
                             Params = [ (Type.Int, "t") ] } ])
            ).SetName("Find definition of view in the same order")
            (
                new TestCaseData(
                    Multiset.ofFlatList
                        [ { Name = "holdTick"
                            Params = [ AExpr (aUnmarked "t") ] }
                          { Name = "holdLock"
                            Params = [] } ]
                )
            ).Returns(
                Some(Multiset.ofFlatList
                         [ { Name = "holdLock"
                             Params = [] }
                           { Name = "holdTick"
                             Params = [ (Type.Int, "t") ] } ])
            ).SetName("Find definition of view in a reversed order")
        ]
