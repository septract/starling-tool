/// <summary>
///     Tests for <c>Graph</c>.
/// </summary>
module Starling.Tests.Graph

open NUnit.Framework

open Starling.Collections
open Starling.Tests.TestUtils
open Starling.Utils
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Expr
open Starling.Core.Graph

/// <summary>
///     Helper to generate a node-pair set from a list.
/// </summary>
let npset : (string * string) list -> Set<(string * string)> = Set.ofList

let oneGFunc (cnd : BoolExpr<Sym<Var>>) (name : string)
  (ps : Expr<Sym<Var>> list)
  : IteratedGFunc<Sym<Var>> =
    iterated (gfunc cnd name ps) (IInt 1L)

/// <summary>
///     Case studies for testing <c>Graph</c>.
/// </summary>
module Studies =
    /// The guarded holdLock view.
    let gHoldLock cnd : IteratedGFunc<Sym<Var>> =
        oneGFunc cnd "holdLock" []

    /// The guarded holdTick view.
    let gHoldTick cnd : IteratedGFunc<Sym<Var>> =
        oneGFunc cnd "holdTick" [normalIntExpr (siVar "t")]

    let ticketLockLockGraph : Graph =
        { Name = "lock"
          Contents =
              Map.ofList
                  [ ("lock_V000",
                     ((Mandatory <| Multiset.empty,
                       Set.singleton
                          { OutEdge.Name = "lock_C000"
                            OutEdge.Dest = "lock_V001"
                            OutEdge.Payload =
                                ECommand
                                    [ command "!ILoad++"
                                           [ normalIntExpr (siVar "t")
                                             normalIntExpr (siVar "ticket") ]
                                           [ normalIntExpr (siVar "t")
                                             normalIntExpr (siVar "ticket")]] },
                       Set.empty,
                       Entry)))
                    ("lock_V001",
                     (Mandatory <| Multiset.singleton (gHoldTick BTrue),
                      Set.singleton
                          { Name = "lock_C004"
                            Dest = "lock_V003"
                            Payload = ECommand [] },
                      Set.singleton
                          { Name = "lock_C000"
                            Src = "lock_V000"
                            Payload =
                                ECommand
                                    [ command "!ILoad++"
                                           [ normalIntExpr (siVar "t")
                                             normalIntExpr (siVar "ticket"); ]
                                           [ normalIntExpr (siVar "t")
                                             normalIntExpr (siVar "ticket") ]] },
                      NodeKind.Normal ))
                    ("lock_V002",
                     (Mandatory <| Multiset.singleton (gHoldLock BTrue),
                      Set.empty,
                      Set.singleton
                          { Name = "lock_C003"
                            Src = "lock_V004"
                            Payload =
                                ECommand
                                    [ Microcode.Assume (iEq (siVar "s") (siVar "t")) ] },
                       Exit))
                    ("lock_V003",
                     (Mandatory <| Multiset.singleton (gHoldTick BTrue),
                      Set.singleton
                          { Name = "lock_C001"
                            Dest = "lock_V004"
                            Payload =
                                ECommand
                                    [ command "!ILoad"
                                           [ normalIntExpr (siVar "s") ]
                                           [ normalIntExpr (siVar "serving") ]] },
                      Set.ofList
                          [ { Name = "lock_C002"
                              Src = "lock_V004"
                              Payload =
                                ECommand
                                  [ Microcode.Assume (BNot (iEq (siVar "s") (siVar "t"))) ] }
                            { Name = "lock_C004"
                              Src = "lock_V001"
                              Payload = ECommand [] } ],
                       NodeKind.Normal))
                    ("lock_V004",
                     (Mandatory <|
                      Multiset.ofFlatList
                          [ gHoldLock (iEq (siVar "s") (siVar "t"))
                            gHoldTick (BNot (iEq (siVar "s") (siVar "t"))) ],
                      Set.ofList
                          [ { Name = "lock_C002"
                              Dest = "lock_V003"
                              Payload =
                                ECommand
                                  [ Microcode.Assume (BNot (iEq (siVar "s") (siVar "t"))) ] }
                            { Name = "lock_C003"
                              Dest = "lock_V002"
                              Payload =
                                ECommand
                                  [ Microcode.Assume (iEq (siVar "s") (siVar "t")) ] } ],
                      Set.singleton
                          { Name = "lock_C001"
                            Src = "lock_V003"
                            Payload =
                                ECommand
                                    [ command "!ILoad"
                                           [ normalIntExpr (siVar "s") ]
                                           [ normalIntExpr (siVar "serving") ]] },

                      NodeKind.Normal)) ] }

    /// The CFG for the ticket lock unlock method.
    let ticketLockUnlockGraph : Graph =
        { Name = "unlock"
          Contents =
              Map.ofList
                  [ ("unlock_V000",
                     (Mandatory <|
                      Multiset.singleton
                              (oneGFunc BTrue "holdLock" [] ),
                      Set.singleton
                          { Name = "unlock_C000"
                            Dest = "unlock_V001"
                            Payload =
                                ECommand
                                    [ command "!I++"
                                           [ normalIntExpr (siVar "serving") ]
                                           [ normalIntExpr (siVar "serving") ]] },
                      Set.empty,
                      Entry))
                    ("unlock_V001",
                     (Mandatory <| Multiset.empty,
                      Set.empty,
                      Set.singleton
                          { Name = "unlock_C000"
                            Src = "unlock_V000"
                            Payload =
                                ECommand
                                    [ command "!I++"
                                           [ normalIntExpr (siVar "serving") ]
                                           [ normalIntExpr (siVar "serving") ]] },
                       Exit)) ] }

    /// The partial CFG for the ticket lock lock method.
    let ticketLockLockSubgraph : Subgraph =
        { Nodes =
              Map.ofList
                  [ ("lock_V000",
                         (Mandatory <| Multiset.empty, Entry))
                    ("lock_V001", (Mandatory <| Multiset.singleton (gHoldTick BTrue), NodeKind.Normal))
                    ("lock_V002", (Mandatory <| Multiset.singleton (gHoldLock BTrue), Exit))
                    ("lock_V003", (Mandatory <| Multiset.singleton (gHoldTick BTrue), NodeKind.Normal))
                    ("lock_V004",
                         (Mandatory <|
                          Multiset.ofFlatList
                             [ gHoldLock (iEq (siVar "s") (siVar "t"))
                               gHoldTick (BNot (iEq (siVar "s") (siVar "t"))) ], NodeKind.Normal)) ]
          Edges =
              Map.ofList
                  [ ("lock_C000",
                         edge "lock_V000"
                              [ command "!ILoad++"
                                     [ normalIntExpr (siVar "t")
                                       normalIntExpr (siVar "ticket") ]
                                     [ normalIntExpr (siVar "t")
                                       normalIntExpr (siVar "ticket") ]]
                              "lock_V001")
                    ("lock_C001",
                         edge "lock_V003"
                              [ command "!ILoad"
                                     [ normalIntExpr (siVar "s") ]
                                     [ normalIntExpr (siVar "serving") ]]
                              "lock_V004")
                    ("lock_C002",
                         edge "lock_V004"
                              [ Microcode.Assume (BNot (iEq (siVar "s") (siVar "t"))) ]
                              "lock_V003")
                    ("lock_C003",
                         edge "lock_V004"
                              [ Microcode.Assume (iEq (siVar "s") (siVar "t")) ]
                              "lock_V002")
                    ("lock_C004",
                         edge "lock_V001"
                              []
                              "lock_V003") ] }

    /// The partial CFG for the ticket lock unlock method.
    let ticketLockUnlockSubgraph : Subgraph =
        { Nodes =
              Map.ofList
                  [ ("unlock_V000",
                         (Mandatory <|
                          Multiset.singleton
                             (oneGFunc BTrue "holdLock" [] ), Entry))
                    ("unlock_V001", (Mandatory <| Multiset.empty, Exit)) ]
          Edges =
               Map.ofList
                  [ ("unlock_C000",
                         edge "unlock_V000"
                              [ command "!I++"
                                     [ normalIntExpr (siVar "serving") ]
                                     [ normalIntExpr (siVar "serving") ]]
                              "unlock_V001" ) ] }


/// <summary>
///     NUnit tests for <c>Graph</c>.
/// </summary>
type NUnit () =
    /// <summary>
    ///     Test cases for checking edge addition.
    /// </summary>
    static member Adds =
        [ TestCaseData(("unlock_N0", "unlock_V001", "unlock_V000"))
            .Returns(
              Some <|
              Map.ofList
                  [ ("unlock_V000",
                     (Mandatory <|
                      Multiset.singleton
                          (Studies.gHoldLock BTrue),
                      Set.singleton
                          { Name = "unlock_C000"
                            Dest = "unlock_V001"
                            Payload =
                                ECommand
                                    [ command "!I++"
                                           [ normalIntExpr (siVar "serving") ]
                                           [ normalIntExpr (siVar "serving") ]] },
                      Set.singleton
                          { Name = "unlock_N0"
                            Src = "unlock_V001"
                            Payload = ECommand [] },
                      Entry ))
                    ("unlock_V001",
                     (Mandatory <| Multiset.empty,
                      Set.singleton
                          { Name = "unlock_N0"
                            Dest = "unlock_V000"
                            Payload = ECommand [] },
                      Set.singleton
                          { Name = "unlock_C000"
                            Src = "unlock_V000"
                            Payload =
                                ECommand
                                    [ command "!I++"
                                           [ normalIntExpr (siVar "serving") ]
                                           [ normalIntExpr (siVar "serving") ]] },
                      Exit)) ] )
            .SetName("Adding a valid, unique edge to unlock works")]

    /// <summary>
    ///     Tests <c>mkEdgeBetween</c>.
    /// </summary>
    [<TestCaseSource("Adds")>]
    member x.``mkEdgeBetween adds edges correctly`` nsd =
          let n, s, d = nsd
          Studies.ticketLockUnlockGraph
          |> mkEdgeBetween s d n (ECommand [])
          |> Option.map (fun g -> g.Contents)


    /// <summary>
    ///     Test cases for checking unification.
    /// </summary>
    static member Unifies =
        [ TestCaseData(("unlock_V001", "unlock_V000"))
            .Returns(
                Some <|
                { Nodes =
                      Map.ofList
                          [ ("unlock_V000",
                             (Mandatory <|
                              Multiset.singleton
                                 (oneGFunc BTrue "holdLock" [] ),
                              EntryExit)) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C000",
                             edge "unlock_V000"
                                  [ command "!I++"
                                          [ normalIntExpr (siVar "serving") ]
                                          [ normalIntExpr (siVar "serving") ]]
                                  "unlock_V000" ) ] } )
            .SetName("unify C1 into C0 on the ticket lock 'unlock'")
          TestCaseData(("unlock_V000", "unlock_V001"))
            .Returns(
                Some <|
                { Nodes =
                      Map.ofList
                          [ ("unlock_V001", (Mandatory <| Multiset.empty,
                                           EntryExit)) ]
                  Edges =
                      Map.ofList
                          [ ("unlock_C000",
                             edge "unlock_V001"
                                  [ command "!I++"
                                          [ normalIntExpr (siVar "serving") ]
                                          [ normalIntExpr (siVar "serving") ]]
                                  "unlock_V001" ) ] } )
            .SetName("unify C0 into C1 on the ticket lock 'unlock'")
          TestCaseData(("unlock_V000", "unlock_V002"))
            .Returns(None)
            .SetName("unifying into non-existent nodes fails")
          TestCaseData(("unlock_V002", "unlock_V000"))
            .Returns(None)
            .SetName("unifying non-existent nodes fails")
          TestCaseData(("unlock_V000", "unlock_V000"))
            .Returns(Some Studies.ticketLockUnlockSubgraph)
            .SetName("unifying a node onto itself does nothing") ]

    /// <summary>
    ///     Tests <c>unify</c>.
    /// </summary>
    [<TestCaseSource("Unifies")>]
    member x.``unify unifies nodes correctly`` st =
          let s, t = st
          Studies.ticketLockUnlockGraph
          |> unify s t
          |> Option.map toSubgraph  // TODO(CaptainHayashi): make unnecessary?


    /// <summary>
    ///     Successful test cases for converting subgraphs to graphs.
    /// </summary>
    static member GoodSubgraphs =
        [ TestCaseData(("empty", { Nodes = Map.empty ; Edges =  Map.empty } ))
            .Returns(Some { Name = "empty" ; Contents = Map.empty } )
            .SetName("The empty subgraph makes a valid graph")
          TestCaseData(("lock", Studies.ticketLockLockSubgraph))
            .Returns(Some Studies.ticketLockLockGraph)
            .SetName("Ticket lock 'lock' subgraph makes a valid graph")
          TestCaseData(("unlock", Studies.ticketLockUnlockSubgraph))
            .Returns(Some Studies.ticketLockUnlockGraph)
            .SetName("Ticket lock 'unlock' subgraph makes a valid graph") ]

    /// <summary>
    ///     Tests <c>graph</c>.
    /// </summary>
    [<TestCaseSource("GoodSubgraphs")>]
    member x.``Valid complete subgraphs can be converted to graphs`` ns =
        let (n, s) = ns
        s |> graph n |> okOption


    // Test cases for InnerView>.
    // (TODO(@MattWindsor91): clean up and rename these)
    /// </summary>
   
    member x.checkInnerView inner outer =
        let extract = match outer with InnerView v -> v
        assertEqual inner extract

    [<Test>]
    member x.``Flattening a mandatory viewexpr returns its view`` () =
        x.checkInnerView 
            (Multiset.singleton
                (gfunc BTrue "holdTick" [ normalIntExpr (siBefore "t") ] ))
            (Mandatory
                (Multiset.singleton
                    (gfunc BTrue "holdTick" [ normalIntExpr (siBefore "t") ] )))

    [<Test>]
    member x.``Flattening an advisory viewexpr returns its view`` () =
        x.checkInnerView 
            (Multiset.singleton
                (gfunc BTrue "holdTick" [ normalIntExpr (siBefore "t") ] ))
            (Advisory
                (Multiset.singleton
                    (gfunc BTrue "holdTick" [ normalIntExpr (siBefore "t") ] )))