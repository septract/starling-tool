/// <summary>
///     Tests for the frontend graph modeller.
/// </summary>
module Starling.Tests.Lang.Grapher

open NUnit.Framework

open Starling.Collections
open Starling.Utils
open Starling.Core.Graph
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
            .Returns(Some { Name = "lock"
                            Contents = ticketLockLockSubgraph } )
            .SetName("Convert the ticket lock 'lock' method to a graph")
          TestCaseData(ticketLockGuardedUnlock)
            .Returns(Some { Name = "unlock"
                            Contents = ticketLockUnlockSubgraph } )
            .SetName("Convert the ticket lock 'unlock' method to a graph") ]

    /// <summary>
    ///     Tests <c>graphMethod</c> on positive cases.
    /// </summary>
    [<TestCaseSource("GoodMethods")>]
    member x.``valid methods are properly converted to graphs`` m =
        m |> graphMethod |> okOption
