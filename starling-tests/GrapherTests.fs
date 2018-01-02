/// <summary>
///     Tests for the frontend graph modeller.
/// </summary>
module Starling.Tests.Lang.Grapher

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Tests.TestUtils

open Starling.Utils
open Starling.Core.Graph
open Starling.Tests.Graph.Studies
open Starling.Lang.Grapher

open Starling.Tests.Studies

[<Test>]
let ``Convert the ticket lock 'lock' method to a subgraph`` () =
    assertEqual
        (Some ticketLockLockSubgraph)
        (okOption (lift toSubgraph (graphMethod "lock" ticketLockLock)))

[<Test>]
let ``Convert the ticket lock 'unlock' method to a subgraph`` () =
    assertEqual
        (Some ticketLockUnlockSubgraph)
        (okOption (lift toSubgraph (graphMethod "unlock" ticketLockUnlock)))
