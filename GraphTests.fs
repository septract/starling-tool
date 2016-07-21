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
                      [ ("lock_V0",
                         ((Mandatory <| Multiset.empty,
                           Set.singleton
                              { OutEdge.Name = "lock_C0"
                                OutEdge.Dest = "lock_V1"
                                OutEdge.Command =
                                    [ command "!ILoad++"
                                           [ "t"; "ticket" ]
                                           [ Typed.Int (siBefore "t")
                                             Typed.Int (siBefore "ticket")]] },
                           Set.empty,
                           Entry)))
                        ("lock_V1",
                         (Mandatory <| Multiset.singleton (gHoldTick BTrue),
                          Set.singleton
                              { Name = "lock_C4"
                                Dest = "lock_V3"
                                Command = [] },
                          Set.singleton
                              { Name = "lock_C0"
                                Src = "lock_V0"
                                Command =
                                    [ command "!ILoad++"
                                           [ "t"; "ticket"; ]
                                           [ Typed.Int (siBefore "t")
                                             Typed.Int (siBefore "ticket") ]] },
                          Normal ))
                        ("lock_V2",
                         (Mandatory <| Multiset.singleton (gHoldLock BTrue),
                          Set.empty,
                          Set.singleton
                              { Name = "lock_C3"
                                Src = "lock_V4"
                                Command =
                                    [ command "Assume" []
                                           [ Typed.Bool
                                                 (iEq (siBefore "s")
                                                      (siBefore "t")) ]] },
                           Exit))
                        ("lock_V3",
                         (Mandatory <| Multiset.singleton (gHoldTick BTrue),
                          Set.singleton
                              { Name = "lock_C1"
                                Dest = "lock_V4"
                                Command =
                                    [ command "!ILoad" 
                                           [ "s" ]
                                           [ Typed.Int (siBefore "serving") ]] },
                          Set.ofList
                              [ { Name = "lock_C2"
                                  Src = "lock_V4"
                                  Command =
                                      [ command "Assume" []
                                             [ Typed.Bool
                                                   (BNot (iEq (siBefore "s")
                                                              (siBefore "t"))) ]] }
                                { Name = "lock_C4"
                                  Src = "lock_V1"
                                  Command = [] } ],
                           Normal))
                        ("lock_V4",
                         (Mandatory <|
                          Multiset.ofFlatList
                              [ gHoldLock (iEq (siVar "s") (siVar "t"))
                                gHoldTick (BNot (iEq (siVar "s") (siVar "t"))) ],
                          Set.ofList
                              [ { Name = "lock_C2"
                                  Dest = "lock_V3"
                                  Command =
                                      [ command "Assume" []
                                             [ Typed.Bool
                                                   (BNot (iEq (siBefore "s")
                                                              (siBefore "t"))) ]] }
                                { Name = "lock_C3"
                                  Dest = "lock_V2"
                                  Command =
                                      [ command "Assume" []
                                             [ Typed.Bool
                                                   (iEq (siBefore "s")
                                                        (siBefore "t")) ]] } ],
                          Set.singleton
                              { Name = "lock_C1"
                                Src = "lock_V3"
                                Command =
                                    [ command "!ILoad"
                                           [ "s" ]
                                           [ Typed.Int (siBefore "serving") ]] },

                          Normal)) ] }

        /// The CFG for the ticket lock unlock method.
        let ticketLockUnlockGraph : Graph =
            { Name = "unlock"
              Contents =
                  Map.ofList
                      [ ("unlock_V0",
                         (Mandatory <|
                          Multiset.singleton
                                  (gfunc BTrue "holdLock" [] ),
                          Set.singleton
                              { Name = "unlock_C0"
                                Dest = "unlock_V1"
                                Command =
                                    [ command "!I++" 
                                           [ "serving" ]
                                           [ Typed.Int (siBefore "serving") ]] },
                          Set.empty,
                          Entry))
                        ("unlock_V1",
                         (Mandatory <| Multiset.empty,
                          Set.empty,
                          Set.singleton
                              { Name = "unlock_C0"
                                Src = "unlock_V0"
                                Command =
                                    [ command "!I++"
                                           [ "serving" ]
                                           [ Typed.Int (siBefore "serving") ]] },
                           Exit)) ] }

        /// The partial CFG for the ticket lock lock method.
        let ticketLockLockSubgraph : Subgraph =
            { Nodes =
                  Map.ofList
                      [ ("lock_V0",
                             (Mandatory <| Multiset.empty, Entry))
                        ("lock_V1", (Mandatory <| Multiset.singleton (gHoldTick BTrue), Normal))
                        ("lock_V2", (Mandatory <| Multiset.singleton (gHoldLock BTrue), Exit))
                        ("lock_V3", (Mandatory <| Multiset.singleton (gHoldTick BTrue), Normal))
                        ("lock_V4",
                             (Mandatory <|
                              Multiset.ofFlatList
                                 [ gHoldLock (iEq (siVar "s") (siVar "t"))
                                   gHoldTick (BNot (iEq (siVar "s") (siVar "t"))) ], Normal)) ]
              Edges =
                  Map.ofList
                      [ ("lock_C0",
                             edge "lock_V0"
                                  [ command "!ILoad++"
                                         [ "t"; "ticket" ]
                                         [ Typed.Int (siBefore "t")
                                           Typed.Int (siBefore "ticket") ]]
                                  "lock_V1")
                        ("lock_C1",
                             edge "lock_V3"
                                  [ command "!ILoad"
                                         [ "s" ]
                                         [ Typed.Int (siBefore "serving") ]]
                                  "lock_V4")
                        ("lock_C2",
                             edge "lock_V4"
                                  [ command "Assume"
                                         []
                                         [ Typed.Bool
                                               (BNot (iEq (siBefore "s")
                                                          (siBefore "t"))) ]]
                                  "lock_V3")
                        ("lock_C3",
                             edge "lock_V4"
                                  [ command "Assume"
                                         []
                                         [ Typed.Bool
                                               (iEq (siBefore "s")
                                                    (siBefore "t")) ]]
                                  "lock_V2")
                        ("lock_C4",
                             edge "lock_V1"
                                  []
                                  "lock_V3") ] }

        /// The partial CFG for the ticket lock unlock method.
        let ticketLockUnlockSubgraph : Subgraph =
            { Nodes =
                  Map.ofList
                      [ ("unlock_V0",
                             (Mandatory <|
                              Multiset.singleton
                                 (svgfunc BTrue "holdLock" [] ), Entry))
                        ("unlock_V1", (Mandatory <| Multiset.empty, Exit)) ]
              Edges =
                   Map.ofList
                      [ ("unlock_C0",
                             edge "unlock_V0"
                                  [ command "!I++"
                                         [ "serving" ] 
                                         [ Typed.Int (siBefore "serving") ]]
                                  "unlock_V1" ) ] }


    /// <summary>
    ///     NUnit tests for <c>Graph</c>.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for checking edge addition.
        /// </summary>
        static member Adds =
            [ TestCaseData(("unlock_N0", "unlock_V1", "unlock_V0"))
                .Returns(
                  Some <|
                  Map.ofList
                      [ ("unlock_V0",
                         (Mandatory <|
                          Multiset.singleton
                              (Studies.gHoldLock BTrue),
                          Set.singleton
                              { Name = "unlock_C0"
                                Dest = "unlock_V1"
                                Command =
                                    [ command "!I++"
                                           [ "serving" ]
                                           [ SMExpr.Int (siBefore "serving") ]] },
                          Set.singleton
                              { Name = "unlock_N0"
                                Src = "unlock_V1"
                                Command = [] },
                          Entry ))
                        ("unlock_V1",
                         (Mandatory <| Multiset.empty,
                          Set.singleton
                              { Name = "unlock_N0"
                                Dest = "unlock_V0"
                                Command = [] },
                          Set.singleton
                              { Name = "unlock_C0"
                                Src = "unlock_V0"
                                Command =
                                    [ command "!I++"
                                           [ "serving" ]
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
            [ TestCaseData(("unlock_V1", "unlock_V0"))
                .Returns(
                    Some <|
                    { Nodes =
                          Map.ofList
                              [ ("unlock_V0",
                                 (Mandatory <|
                                  Multiset.singleton
                                     (gfunc BTrue "holdLock" [] ),
                                  EntryExit)) ]
                      Edges =
                          Map.ofList
                              [ ("unlock_C0",
                                 edge "unlock_V0"
                                      [ command "!I++"
                                              [ "serving" ]
                                              [ SMExpr.Int (siBefore "serving") ]]
                                      "unlock_V0" ) ] } )
                .SetName("unify C1 into C0 on the ticket lock 'unlock'")
              TestCaseData(("unlock_V0", "unlock_V1"))
                .Returns(
                    Some <|
                    { Nodes =
                          Map.ofList
                              [ ("unlock_V1", (Mandatory <| Multiset.empty,
                                               EntryExit)) ]
                      Edges =
                          Map.ofList
                              [ ("unlock_C0",
                                 edge "unlock_V1"
                                      [ command "!I++"
                                              [ "serving" ] 
                                              [ SMExpr.Int (siBefore "serving") ]]
                                      "unlock_V1" ) ] } )
                .SetName("unify C0 into C1 on the ticket lock 'unlock'")
              TestCaseData(("unlock_V0", "unlock_V2"))
                .Returns(None)
                .SetName("unifying into non-existent nodes fails")
              TestCaseData(("unlock_V2", "unlock_V0"))
                .Returns(None)
                .SetName("unifying non-existent nodes fails")
              TestCaseData(("unlock_V0", "unlock_V0"))
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
            (ve : ViewExpr<SMGView>) =
            match ve with InnerView v -> v
