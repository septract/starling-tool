/// <summary>
///     Tests for the graph construction and inspection functions.
/// </summary>
module Starling.Tests.Core.Graph

open NUnit.Framework

open Starling.Core.Graph

open Starling.Tests.Studies


/// <summary>
///     Helper to generate a node-pair set from a list.
/// </summary>
let npset : (string * string) list -> Set<(string * string)> = Set.ofList

/// <summary>
///     Test class for the graph construction and inspection functions.
/// </summary>
type GraphTests() =
    /// <summary>
    ///     Test cases for checking node pair generation.
    /// </summary>
    static member NodePairs =
        [ TestCaseData({ Nodes = Map.empty ; Edges = Map.empty })
            .Returns(npset [])
            .SetName("Extract 0 node pairs from the empty graph")
          TestCaseData(ticketLockUnlockSubgraph)
            .Returns(npset [ ("unlock_V0", "unlock_V1") ] )
            .SetName("Extract 1 node pair from the ticketed lock 'unlock'")
          TestCaseData(ticketLockLockSubgraph)
            .Returns(npset [ ("lock_V0", "lock_V1")
                             ("lock_V0", "lock_V2")
                             ("lock_V0", "lock_V3")
                             ("lock_V0", "lock_V4")
                             ("lock_V1", "lock_V2")
                             ("lock_V1", "lock_V3")
                             ("lock_V1", "lock_V4")
                             ("lock_V2", "lock_V3")
                             ("lock_V2", "lock_V4")
                             ("lock_V3", "lock_V4") ] )
            .SetName("Extract 10 node pairs from the ticketed lock 'lock'") ]

    /// <summary>
    ///     Tests <c>nodePairs</c>.
    /// </summary>
    [<TestCaseSource("NodePairs")>]
    member x.``nodePairs extracts node pairs properly`` sg =
        sg |> nodePairs |> Set.ofSeq
