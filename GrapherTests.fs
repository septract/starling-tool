/// <summary>
///     Tests for the frontend graph modeller.
/// </summary>
module Starling.Tests.Lang.Grapher

open Chessie.ErrorHandling
open NUnit.Framework

open Starling.Utils
open Starling.Core.Graph
open Starling.Tests.Graph.Tests.Studies
open Starling.Lang.Grapher

open Starling.Tests.Studies


/// <summary>
///     Test class for the frontend graph modeller.
/// </summary>
module Tests =
    open Starling.Utils.Testing

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
