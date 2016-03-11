/// <summary>
///     Tests for the graph construction and inspection functions.
/// </summary>
module Starling.Tests.Core.Graph

open NUnit.Framework

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Graph
open Starling.Core.Model

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
    ///     Test cases for checking unification.
    /// </summary>
    static member Unifies =
        [ TestCaseData(("unlock_V1", "unlock_V0"))
            .Returns(
                { Nodes =
                      Map.ofList
                          [ ("unlock_V0",
                             Multiset.singleton
                                 (gfunc BTrue "holdLock" [] )) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C0",
                             edge "unlock_V0"
                                  (func "!I++"
                                        [ AExpr (aBefore "serving")
                                          AExpr (aAfter "serving") ] )
                                  "unlock_V0" ) ] } )
            .SetName("unify C1 into C0 on the ticketed lock 'unlock'")
          TestCaseData(("unlock_V0", "unlock_V1"))
            .Returns(
                { Nodes =
                      Map.ofList
                          [ ("unlock_V1", Multiset.empty () ) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C0",
                             edge "unlock_V1"
                                  (func "!I++"
                                        [ AExpr (aBefore "serving")
                                          AExpr (aAfter "serving") ] )
                                  "unlock_V1" ) ] } )
            .SetName("unify C0 into C1 on the ticketed lock 'unlock'")
          TestCaseData(("unlock_V0", "unlock_V2"))
            .Returns(
                { Nodes =
                      Map.ofList
                          [ ("unlock_V1", Multiset.empty () ) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C0",
                             edge "unlock_V2"
                                  (func "!I++"
                                        [ AExpr (aBefore "serving")
                                          AExpr (aAfter "serving") ] )
                                  "unlock_V1" ) ] } )
            .SetName("unifying into non-existent nodes is possible")
          TestCaseData(("unlock_V2", "unlock_V0"))
            .Returns(ticketLockUnlockSubgraph)
            .SetName("unifying non-existent nodes does nothing")
          TestCaseData(("unlock_V0", "unlock_V0"))
            .Returns(ticketLockUnlockSubgraph)
            .SetName("unifying a node onto itself does nothing") ]

    /// <summary>
    ///     Tests <c>unify</c>.
    /// </summary>
    [<TestCaseSource("Unifies")>]
    member x.``unify unifies nodes correctly`` tc =
          uncurry (unify ticketLockUnlockSubgraph) tc

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
