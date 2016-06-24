/// <summary>
///     Tests for the frontend graph modeller.
/// </summary>
module Starling.Tests.Lang.Grapher

open Chessie.ErrorHandling
open NUnit.Framework

open Starling.Utils
open Starling.Core.Graph
open Starling.Core.Graph.Tests.Studies
open Starling.Lang.Grapher

open Starling.Tests.Studies


/// <summary>
///     Test class for the frontend graph modeller.
/// </summary>
type GrapherTests() =
    /// <summary>
    ///     Positive test cases for converting methods to graphs.
    /// </summary>
    static member GoodMethods =
        [ TestCaseData(ticketLockGuardedLock)
            .Returns(Some ticketLockLockSubgraph)
            .SetName("Convert the ticket lock 'lock' method to a graph")
          TestCaseData(ticketLockGuardedUnlock)
            .Returns(Some ticketLockUnlockSubgraph)
            .SetName("Convert the ticket lock 'unlock' method to a graph") ]

    /// <summary>
    ///     Tests <c>graphMethod</c> on positive cases.
    /// </summary>
    [<TestCaseSource("GoodMethods")>]
    member x.``valid methods are properly converted to graphs`` m =
        // TODO(CaptainHayashi): don't convert down to subgraphs
        m |> graphMethod |> lift toSubgraph |> okOption
