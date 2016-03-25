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
open Starling.Core.GuardedView

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
    ///     Test cases for checking edge addition.
    /// </summary>
    static member Adds =
        [ TestCaseData(("unlock_N0", "unlock_V1", "unlock_V0"))
            .Returns(
              Some <|
              Map.ofList
                  [ ("unlock_V0",
                     (Multiset.singleton
                          (gHoldLock BTrue),
                      Set.singleton
                          { Name = "unlock_C0"
                            Dest = "unlock_V1"
                            Command =
                                [ func "!I++"
                                       [ AExpr (aBefore "serving")
                                         AExpr (aAfter "serving") ]] },
                      Set.singleton
                          { Name = "unlock_N0"
                            Src = "unlock_V1"
                            Command = [] },
                      Entry ))
                    ("unlock_V1",
                     (Multiset.empty (),
                      Set.singleton
                          { Name = "unlock_N0"
                            Dest = "unlock_V0"
                            Command = [] },
                      Set.singleton
                          { Name = "unlock_C0"
                            Src = "unlock_V0"
                            Command =
                                [ func "!I++"
                                       [ AExpr (aBefore "serving")
                                         AExpr (aAfter "serving") ]] },
                      Exit)) ] )
            .SetName("Adding a valid, unique edge to unlock works")]

    /// <summary>
    ///     Tests <c>unify</c>.
    /// </summary>
    [<TestCaseSource("Adds")>]
    member x.``mkEdgeBetween adds edges correctly`` nsd =
          let n, s, d = nsd
          ticketLockUnlockGraph
          |> mkEdgeBetween s d n []
          |> Option.map (fun g -> g.Contents)


    /// <summary>
    ///     Test cases for checking unification.
    /// </summary>
    static member Unifies =
        [ TestCaseData(("unlock_V1", "unlock_V0"))
            .Returns(
                Some <|
                { Nodes =
                      Map.ofList
                          [ ("unlock_V0",
                             (Multiset.singleton
                                 (gfunc BTrue "holdLock" [] ),
                              EntryExit)) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C0",
                             edge "unlock_V0"
                                  [ func "!I++"
                                          [ AExpr (aBefore "serving")
                                            AExpr (aAfter "serving") ]]
                                  "unlock_V0" ) ] } )
            .SetName("unify C1 into C0 on the ticket lock 'unlock'")
          TestCaseData(("unlock_V0", "unlock_V1"))
            .Returns(
                Some <|
                { Nodes =
                      Map.ofList
                          [ ("unlock_V1", (Multiset.empty (), EntryExit)) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C0",
                             edge "unlock_V1"
                                  [ func "!I++"
                                          [ AExpr (aBefore "serving")
                                            AExpr (aAfter "serving") ]]
                                  "unlock_V1" ) ] } )
            .SetName("unify C0 into C1 on the ticket lock 'unlock'")
          TestCaseData(("unlock_V0", "unlock_V2"))
            .Returns(None)
            .SetName("unifying into non-existent nodes fails")
          TestCaseData(("unlock_V2", "unlock_V0"))
            .Returns(None)
            .SetName("unifying non-existent nodes fails")
          TestCaseData(("unlock_V0", "unlock_V0"))
            .Returns(Some ticketLockUnlockSubgraph)
            .SetName("unifying a node onto itself does nothing") ]

    /// <summary>
    ///     Tests <c>unify</c>.
    /// </summary>
    [<TestCaseSource("Unifies")>]
    member x.``unify unifies nodes correctly`` st =
          let s, t = st
          ticketLockUnlockGraph
          |> unify s t
          |> Option.map toSubgraph  // TODO(CaptainHayashi): make unnecessary?


    /// <summary>
    ///     Successful test cases for converting subgraphs to graphs.
    /// </summary>
    static member GoodSubgraphs =
        [ TestCaseData(("empty", { Nodes = Map.empty ; Edges =  Map.empty } ))
            .Returns(Some { Name = "empty" ; Contents = Map.empty } )
            .SetName("The empty subgraph makes a valid graph")
          TestCaseData(("lock", ticketLockLockSubgraph))
            .Returns(Some ticketLockLockGraph)
            .SetName("Ticket lock 'lock' subgraph makes a valid graph")
          TestCaseData(("unlock", ticketLockUnlockSubgraph))
            .Returns(Some ticketLockUnlockGraph)
            .SetName("Ticket lock 'unlock' subgraph makes a valid graph") ]

    /// <summary>
    ///     Tests <c>graph</c>.
    /// </summary>
    [<TestCaseSource("GoodSubgraphs")>]
    member x.``Valid complete subgraphs can be converted to graphs`` ns =
        let (n, s) = ns
        s |> graph n |> okOption
