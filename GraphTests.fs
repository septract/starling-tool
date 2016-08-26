/// <summary>
///     Tests for <c>Graph</c>.
/// </summary>
module Starling.Tests.Graph

open Starling.Collections
open Starling.Utils
open Starling.Core.Model
open Starling.Core.Axiom
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Expr

module Tests =
    open Starling.Core.Graph

    open Starling.Core.GuardedView

    open NUnit.Framework
    open Starling.Core.TypeSystem
    open Starling.Utils.Testing

    /// <summary>
    ///     Helper to generate a node-pair set from a list.
    /// </summary>
    let npset : (string * string) list -> Set<(string * string)> = Set.ofList

    /// <summary>
    ///     Case studies for testing <c>Graph</c>.
    /// </summary>
    module Studies =
        /// The guarded holdLock view.
        let gHoldLock cnd : SVGFunc = svgfunc cnd "holdLock" []

        /// The guarded holdTick view.
        let gHoldTick cnd : SVGFunc = svgfunc cnd "holdTick" [SVExpr.Int (siVar "t")]

        let ticketLockLockGraph : Graph =
            { Name = "lock"
              Contents =
                  Map.ofList
                      [ ("lock_V000",
                         ((Mandatory <| Multiset.empty,
                           Set.singleton
                              { OutEdge.Name = "lock_C000"
                                OutEdge.Dest = "lock_V001"
                                OutEdge.Command =
                                    [ command "!ILoad++"
                                           [ Int "t"; Int "ticket" ]
                                           [ Typed.Int (siBefore "t")
                                             Typed.Int (siBefore "ticket")]] },
                           Set.empty,
                           Entry)))
                        ("lock_V001",
                         (Mandatory <| Multiset.singleton (gHoldTick BTrue),
                          Set.singleton
                              { Name = "lock_C004"
                                Dest = "lock_V003"
                                Command = [] },
                          Set.singleton
                              { Name = "lock_C000"
                                Src = "lock_V000"
                                Command =
                                    [ command "!ILoad++"
                                           [ Int "t"; Int "ticket"; ]
                                           [ Typed.Int (siBefore "t")
                                             Typed.Int (siBefore "ticket") ]] },
                          Normal ))
                        ("lock_V002",
                         (Mandatory <| Multiset.singleton (gHoldLock BTrue),
                          Set.empty,
                          Set.singleton
                              { Name = "lock_C003"
                                Src = "lock_V004"
                                Command =
                                    [ command "Assume" []
                                           [ Typed.Bool
                                                 (iEq (siBefore "s")
                                                      (siBefore "t")) ]] },
                           Exit))
                        ("lock_V003",
                         (Mandatory <| Multiset.singleton (gHoldTick BTrue),
                          Set.singleton
                              { Name = "lock_C001"
                                Dest = "lock_V004"
                                Command =
                                    [ command "!ILoad" 
                                           [ Int "s" ]
                                           [ Typed.Int (siBefore "serving") ]] },
                          Set.ofList
                              [ { Name = "lock_C002"
                                  Src = "lock_V004"
                                  Command =
                                      [ command "Assume" []
                                             [ Typed.Bool
                                                   (BNot (iEq (siBefore "s")
                                                              (siBefore "t"))) ]] }
                                { Name = "lock_C004"
                                  Src = "lock_V001"
                                  Command = [] } ],
                           Normal))
                        ("lock_V004",
                         (Mandatory <|
                          Multiset.ofFlatList
                              [ gHoldLock (iEq (siVar "s") (siVar "t"))
                                gHoldTick (BNot (iEq (siVar "s") (siVar "t"))) ],
                          Set.ofList
                              [ { Name = "lock_C002"
                                  Dest = "lock_V003"
                                  Command =
                                      [ command "Assume" []
                                             [ Typed.Bool
                                                   (BNot (iEq (siBefore "s")
                                                              (siBefore "t"))) ]] }
                                { Name = "lock_C003"
                                  Dest = "lock_V002"
                                  Command =
                                      [ command "Assume" []
                                             [ Typed.Bool
                                                   (iEq (siBefore "s")
                                                        (siBefore "t")) ]] } ],
                          Set.singleton
                              { Name = "lock_C001"
                                Src = "lock_V003"
                                Command =
                                    [ command "!ILoad"
                                           [ Int "s" ]
                                           [ Typed.Int (siBefore "serving") ]] },

                          Normal)) ] }

        /// The CFG for the ticket lock unlock method.
        let ticketLockUnlockGraph : Graph =
            { Name = "unlock"
              Contents =
                  Map.ofList
                      [ ("unlock_V000",
                         (Mandatory <|
                          Multiset.singleton
                                  (gfunc BTrue "holdLock" [] ),
                          Set.singleton
                              { Name = "unlock_C000"
                                Dest = "unlock_V001"
                                Command =
                                    [ command "!I++" 
                                           [ Int "serving" ]
                                           [ Typed.Int (siBefore "serving") ]] },
                          Set.empty,
                          Entry))
                        ("unlock_V001",
                         (Mandatory <| Multiset.empty,
                          Set.empty,
                          Set.singleton
                              { Name = "unlock_C000"
                                Src = "unlock_V000"
                                Command =
                                    [ command "!I++"
                                           [ Int "serving" ]
                                           [ Typed.Int (siBefore "serving") ]] },
                           Exit)) ] }

        /// The partial CFG for the ticket lock lock method.
        let ticketLockLockSubgraph : Subgraph =
            { Nodes =
                  Map.ofList
                      [ ("lock_V000",
                             (Mandatory <| Multiset.empty, Entry))
                        ("lock_V001", (Mandatory <| Multiset.singleton (gHoldTick BTrue), Normal))
                        ("lock_V002", (Mandatory <| Multiset.singleton (gHoldLock BTrue), Exit))
                        ("lock_V003", (Mandatory <| Multiset.singleton (gHoldTick BTrue), Normal))
                        ("lock_V004",
                             (Mandatory <|
                              Multiset.ofFlatList
                                 [ gHoldLock (iEq (siVar "s") (siVar "t"))
                                   gHoldTick (BNot (iEq (siVar "s") (siVar "t"))) ], Normal)) ]
              Edges =
                  Map.ofList
                      [ ("lock_C000",
                             edge "lock_V000"
                                  [ command "!ILoad++"
                                         [ Int "t"; Int "ticket" ]
                                         [ Typed.Int (siBefore "t")
                                           Typed.Int (siBefore "ticket") ]]
                                  "lock_V001")
                        ("lock_C001",
                             edge "lock_V003"
                                  [ command "!ILoad"
                                         [ Int "s" ]
                                         [ Typed.Int (siBefore "serving") ]]
                                  "lock_V004")
                        ("lock_C002",
                             edge "lock_V004"
                                  [ command "Assume"
                                         []
                                         [ Typed.Bool
                                               (BNot (iEq (siBefore "s")
                                                          (siBefore "t"))) ]]
                                  "lock_V003")
                        ("lock_C003",
                             edge "lock_V004"
                                  [ command "Assume"
                                         []
                                         [ Typed.Bool
                                               (iEq (siBefore "s")
                                                    (siBefore "t")) ]]
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
                                 (svgfunc BTrue "holdLock" [] ), Entry))
                        ("unlock_V001", (Mandatory <| Multiset.empty, Exit)) ]
              Edges =
                   Map.ofList
                      [ ("unlock_C000",
                             edge "unlock_V000"
                                  [ command "!I++"
                                         [ Int "serving" ] 
                                         [ Typed.Int (siBefore "serving") ]]
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
                                Command =
                                    [ command "!I++"
                                           [ Int "serving" ]
                                           [ SMExpr.Int (siBefore "serving") ]] },
                          Set.singleton
                              { Name = "unlock_N0"
                                Src = "unlock_V001"
                                Command = [] },
                          Entry ))
                        ("unlock_V001",
                         (Mandatory <| Multiset.empty,
                          Set.singleton
                              { Name = "unlock_N0"
                                Dest = "unlock_V000"
                                Command = [] },
                          Set.singleton
                              { Name = "unlock_C000"
                                Src = "unlock_V000"
                                Command =
                                    [ command "!I++"
                                           [ Int "serving" ]
                                           [ SMExpr.Int (siBefore "serving") ]] },
                          Exit)) ] )
                .SetName("Adding a valid, unique edge to unlock works")]

        /// <summary>
        ///     Tests <c>mkEdgeBetween</c>.
        /// </summary>
        [<TestCaseSource("Adds")>]
        member x.``mkEdgeBetween adds edges correctly`` nsd =
              let n, s, d = nsd
              Studies.ticketLockUnlockGraph
              |> mkEdgeBetween s d n []
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
                                     (gfunc BTrue "holdLock" [] ),
                                  EntryExit)) ]
                      Edges =
                          Map.ofList
                              [ ("unlock_C000",
                                 edge "unlock_V000"
                                      [ command "!I++"
                                              [ Int "serving" ]
                                              [ SMExpr.Int (siBefore "serving") ]]
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
                                              [ Int "serving" ] 
                                              [ SMExpr.Int (siBefore "serving") ]]
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


        /// <summary>
        ///     Test cases for <c>InnerView</c>.
        /// </summary>
        static member ViewExprFlattens =
            [ TestCaseData(Mandatory (Multiset.singleton (smgfunc BTrue "holdLock" [])))
                  .Returns(Multiset.singleton (smgfunc BTrue "holdLock" []))
                  .SetName("Flattening a mandatory viewexpr returns its view")
              TestCaseData(Advisory
                               (Multiset.singleton
                                    (smgfunc BTrue "holdTick"
                                         [ SMExpr.Int (siBefore "t") ] )))
                  .Returns(Multiset.singleton
                               (smgfunc BTrue "holdTick"
                                    [ SMExpr.Int (siBefore "t") ] ))
                  .SetName("Flattening an advisory viewexpr returns its view") ]

        /// <summary>
        ///     Tests <c>InnerView</c>.
        /// </summary>
        [<TestCaseSource("ViewExprFlattens")>]
        member x.``View expressions can be flattened into views``
            (ve : ViewExpr<GView<Sym<MarkedVar>>>) =
            match ve with InnerView v -> v
