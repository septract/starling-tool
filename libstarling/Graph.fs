/// <summary>
///     Types and helper functions for Starling control-flow graphs.
///
///     <para>
///         Starling CFGs contain one node per view assertion, and one edge
///         per command.
///     </para>
/// </summary>
module Starling.Core.Graph

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Model
open Starling.Core.Axiom
open Starling.Core.Command
open Starling.Core.GuardedView
open Starling.Core.Symbolic
open Starling.Core.Traversal


/// <summary>
///     Pretty printers for control-flow graphs.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A view of the type permitted in a Graph.
    /// </summary>
    type GraphView = GView<Sym<Var>>

    /// <summary>
    ///     A <see cref="ViewExpr"/> of the type permitted in a Graph.
    /// </summary>
    type GraphViewExpr = ViewExpr<GraphView>

    /// <summary>
    ///     An edge identifier.
    /// </summary>
    type EdgeID = string

    /// <summary>
    ///     A node identifier.
    /// </summary>
    type NodeID = string

    /// <summary>
    ///     Enumeration of node types.
    ///
    ///     <para>
    ///         Used to signify if a node is an Entry or Edit node
    ///     </para>
    /// </summary>
    type NodeKind = Normal | Entry | Exit | EntryExit

    /// <summary>
    ///     Type for graph edges.
    /// </summary>
    type Edge =
    | /// <summary>
      ///     An edge corresponding to a miracle command.
      ///
      ///     <para>
      ///         Miracles are holes in the CFG, but we represent them
      ///         as edges for simplicity.
      ///     </para>
      /// </summary>
      MiracleEdge of source : NodeID * target : NodeID
    | /// <summary>
      ///     An edge with a command across it.
      ///
      ///     <para>
      ///         Command edges are axioms, in that they directly correspond to
      ///         Hoare triples.
      ///     </para>
      /// </summary>
      CommandEdge of Axiom<NodeID, Command>

    /// <summary>The payload of an edge in a full graph.</summary>
    type EdgePayload =
    | /// <summary>An edge carrying a command.</summary>
      ECommand of Command
    | /// <summary>An edge carrying a miracle.</summary>
      EMiracle

    /// <summary>
    ///     The container for a partial control-flow graph.
    ///
    ///     <para>
    ///         Partial graphs use an inefficient representation.  Once
    ///         complete, they may be converted into <c>Graph</c>s.
    ///     </para>
    /// </summary>
    type Subgraph =
        {
            /// <summary>
            ///     Set of nodes in the control-flow graph.
            /// </summary>
            Nodes: Map<NodeID, GraphViewExpr * NodeKind>

            /// <summary>
            ///     Set of edges in the control-flow graph.
            /// </summary>
            Edges: Map<EdgeID, Edge>
        }

    /// <summary>
    ///     An in edge in a standalone control-flow graph.
    /// </summary>
    type InEdge =
        { /// <summary>
          ///      The name of the edge.
          /// </summary>
          Name : EdgeID
          /// <summary>
          ///      The source of this edge.
          /// </summary>
          Src : NodeID
          /// <summary>
          ///      The payload this edge carries.
          /// </summary>
          Payload : EdgePayload }

    /// <summary>
    ///     An out edge in a standalone control-flow graph.
    /// </summary>
    type OutEdge =
        { /// <summary>
          ///      The name of the edge.
          /// </summary>
          Name : EdgeID
          /// <summary>
          ///      The destination of this edge.
          /// </summary>
          Dest : NodeID
          /// <summary>
          ///      The payload this edge carries.
          /// </summary>
          Payload : EdgePayload }

    /// <summary>
    ///     A fully resolved edge, containing views.
    /// </summary>
    type FullEdge =
        { /// <summary>
          ///     The name of the edge.
          /// </summary>
          Name : EdgeID
          /// <summary>
          ///     The name of the source node.
          /// </summary>
          SrcName : NodeID
          /// <summary>
          ///     The view of the source node.
          /// </summary>
          SrcView : GraphViewExpr
          /// <summary>
          ///     The name of the destination node.
          /// </summary>
          DestName : NodeID
          /// <summary>
          ///     The view of the destination node.
          /// </summary>
          DestView : GraphViewExpr
          /// <summary>
          ///      The payload this edge carries.
          /// </summary>
          Payload : EdgePayload }

    /// <summary>
    ///     A standalone control-flow graph.
    ///
    ///     <para>
    ///         Control-flow graphs use an adjacency list format.
    ///     </para>
    /// </summary>
    type Graph = {
        /// <summary>
        ///     The name of the graph.
        /// </summary>
        Name : string
        /// <summary>
        ///     The contents of the graph.
        /// </summary>
        Contents : Map<
            NodeID,
            (GraphViewExpr
             * Set<OutEdge>
             * Set<InEdge>
             * NodeKind)> }

    /// <summary>
    ///     Type of Chessie errors for CFG actions.
    /// </summary>
    type Error =
        /// <summary>
        ///     The given edge has an invalid node index.
        /// </summary>
        | EdgeOutOfBounds of id : EdgeID * edge : Edge
        /// <summary>
        ///     The given node was duplicated when trying to merge graphs.
        /// </summary>
        | DuplicateNode of id: NodeID
        /// <summary>
        ///     The given edge was duplicated when trying to merge graphs.
        /// </summary>
        | DuplicateEdge of id: EdgeID
        /// <summary>
        ///     A traversal used in graph processing failed.
        /// </summary>
        | Traversal of err : TraversalError<Error>

/// <summary>
///     Creates a single miracle <c>Edge</c>.
/// </summary>
/// <param name="p">
///     The source view.
/// </param>
/// <param name="q">
///     The target view.
/// </param>
/// <returns>
///     An <c>Edge</c> with the above properties.
/// </returns>
let medge (p : NodeID) (q : NodeID) : Edge =
    MiracleEdge (p, q)


/// <summary>
///     Creates a single command <c>Edge</c>.
/// </summary>
/// <param name="p">
///     The source view.
/// </param>
/// <param name="c">
///     The command making up the edge.
/// </param>
/// <param name="q">
///     The target view.
/// </param>
/// <returns>
///     An <c>Edge</c> with the above properties.
/// </returns>
let edge (p : NodeID) (c : Command) (q : NodeID) : Edge =
    CommandEdge (axiom p c q)

/// <summary>
///     Converts a <c>Graph</c> to a <c>Subgraph</c>.
/// </summary>
/// <param name="graph">
///     The graph to convert to a subgraph.
/// </param>
/// <returns>
///     A <c>Subgraph</c> giving the same nodes and edges as
///     <paramref name="graph" />.
/// </returns>
let toSubgraph (graph : Graph) : Subgraph =
    { Nodes =
          graph.Contents
          |> Map.toSeq
          |> Seq.map (fun (nodeName, (nodeView, _, _, nodeKind)) -> (nodeName, (nodeView, nodeKind)))
          |> Map.ofSeq
      Edges =
          graph.Contents
          |> Map.toSeq
          |> Seq.map
                 (fun (fromName, (_, outEdges, _, _)) ->
                      Seq.map
                          (fun { Name = n; Dest = toName; Payload = p } ->
                            (n,
                                match p with
                                | ECommand cmd -> edge fromName cmd toName
                                | EMiracle -> medge fromName toName))
                          outEdges)
          |> Seq.concat
          |> Map.ofSeq }

/// <summary>
///     Converts a subgraph to a standalone graph.
/// </summary>
/// <param name="name">
///     The name to give the standalone graph.
/// </param>
/// <param name="sg">
///     The subgraph to check.
/// </param>
/// <returns>
///     A <c>Graph</c>, wrapped in a Chessie result over <c>Error</c>.
///     If the edges are valid (reference indices in <paramref
///     name="nodes" />), then the result will be <c>ok</c>.
/// </returns>
let graph (name : string) (sg : Subgraph) : Result<Graph, Error> =
    // Are any of the node indices out of bounds?
    let oob s t = not (Map.containsKey s sg.Nodes && Map.containsKey t sg.Nodes)
    let oobEdges =
        seq {
            for edge in sg.Edges do
                match edge.Value with
                | CommandEdge { Pre = s; Post = t } ->
                    if oob s t then yield EdgeOutOfBounds (edge.Key, edge.Value)
                | MiracleEdge _ -> () }
    if Seq.isEmpty oobEdges
    then
        let processNode nodeName (nodeView, nodeKind) =
            let mkOutEdge n src dst p : OutEdge option =
                if src = nodeName
                then Some { Name = n; Payload = p; Dest = dst }
                else None
            let outEdges =
                sg.Edges
                |> Map.toSeq
                |> Seq.choose
                    (fun (edgeName, edge) ->
                        match edge with
                        | CommandEdge { Pre = src; Post = dst; Cmd = cmd } ->
                            mkOutEdge edgeName src dst (ECommand cmd)
                        | MiracleEdge (src, dst) ->
                            mkOutEdge edgeName src dst EMiracle)
                |> Set.ofSeq
            let mkInEdge n src dst p : InEdge option =
                if dst = nodeName
                then Some { Name = n; Payload = p; Src = src }
                else None
            let inEdges =
                sg.Edges
                |> Map.toSeq
                |> Seq.choose
                    (fun (edgeName, edge) ->
                        match edge with
                        | CommandEdge { Pre = src; Post = dst; Cmd = cmd } ->
                            mkInEdge edgeName src dst (ECommand cmd)
                        | MiracleEdge (src, dst) ->
                            mkInEdge edgeName src dst EMiracle)
                |> Set.ofSeq
            (nodeView, outEdges, inEdges, nodeKind)

        ok { Name = name; Contents = Map.map processNode sg.Nodes }
    else Bad (List.ofSeq oobEdges)

/// <summary>
///    Combines two subgraphs.
/// </summary>
/// <param name="_arg1">
///    The first graph to combine.
/// </param>
/// <param name="_arg2">
///    The second graph to combine.
/// </param>
/// <returns>
///     A <c>Subgraph</c>, wrapped in a Chessie result over <c>Error</c>.
///     If the two graphs do not contain duplicate
///     nodes, then the result will be <c>ok</c>.
///     The graph will contain the nodes and edges from <paramref
///     name="_arg1" /> and <paramref name="_arg2" />.
/// </returns>
let combine
  ({ Nodes = ans ; Edges = aes } : Subgraph)
  ({ Nodes = bns ; Edges = bes } : Subgraph)
  : Result<Subgraph, Error> =
    match (keyDuplicates ans bns |> Seq.toList,
           keyDuplicates aes bes |> Seq.toList) with
    | ([], []) -> { Nodes = mapAppend ans bns
                    Edges = mapAppend aes bes } |> ok
    | (xs, ys) -> List.append (xs |> List.map DuplicateNode)
                              (ys |> List.map DuplicateEdge)
                  |> Bad


(*
 * Graph transformations.
 *)

/// <summary>
///     Unifies two nodes in a graph.
/// </summary>
/// <param name="src">
///     The node to delete in the unification.
/// </param>
/// <param name="dest">
///     The node to keep in the unification.
/// </param>
/// <param name="graph">
///     The subgraph to transform.
/// </param>
/// <returns>
///     An Option.
///     The option is <c>None</c> if either of the nodes do not exist.
///     It is <c>Some</c> <paramref name="graph" /> if
///     <paramref name="src" /> = <paramref name="dest" />.
///     Otherwise, it contains the graph that is <paramref name="graph" />
///     but with <paramref name="src" /> deleted, and all edges starting
///     and ending at it redirected to <paramref name="dest" />.
/// </returns>
let unify (src : NodeID) (dest : NodeID) (graph : Graph) : Graph option =
    if (src = dest)
    then Some graph
    else if (not (Map.containsKey src graph.Contents))
            || (not (Map.containsKey dest graph.Contents))
    then None
    else
        // Pull out the source's entry, ready to append later.
        let _, srcOut, srcIn, nodeKind = graph.Contents.[src]

        let swapNode = function
                       | n when n = src -> dest
                       | n -> n
        let swapIn o = { o with Src = swapNode o.Src }
        let swapOut o = { o with Dest = swapNode o.Dest }

        (* Unify Node Kinds to account for Entry and Exit combining *)
        let unifyNodeKind nk1 nk2 =
            match nk1, nk2 with
            | Entry, Exit  | Exit, Entry
            | EntryExit, _ | _, EntryExit -> EntryExit
            | Entry, _     | _, Entry     -> Entry
            | Exit, _      | _, Exit      -> Exit
            | Normal, Normal              -> Normal

        (* Remove a node if it is source;
         * otherwise, inspect its nodes for source, and rewrite them
         * to target.  If the node is target, add in the source edges.
         *)
        let unifyStep (name, (view, outEdges, inEdges, nodeKind2)) =
            if name = src
            then None
            else
                let newOut =
                    outEdges
                    |> Set.map swapOut
                    |> if name = dest then Set.union srcOut else id
                let newIn =
                    inEdges
                    |> Set.map swapIn
                    |> if name = dest then Set.union srcIn else id

                (* If we are the destination, then we need to merge in the
                   source's node kind. *)
                let newNodeKind =
                    if name = dest
                    then unifyNodeKind nodeKind nodeKind2
                    else nodeKind2

                Some (name, (view, newOut, newIn, newNodeKind))

        let contents =
            graph.Contents
            |> Map.toSeq
            |> Seq.choose unifyStep
            |> Map.ofSeq

        Some { graph with Contents = contents }


/// <summary>
///     Performs an operation on the out and in edges of two nodes in the
///     graph.
///
///     <para>
///         The two nodes need not be disjoint.
///     </para>
/// </summary>
/// <param name="f">
///     The function to apply.
///     This receives two parameters: the out and in nodes
///     for <paramref name="x" /> and <paramref name="y" />
///     respectively.
/// </param>
/// <param name="x">
///     The first node's ID.
/// </param>
/// <param name="y">
///     The second node's ID.
/// </param>
/// <param name="graph">
///     The graph to change.
/// </param>
/// <returns>
///     An Option.
///     If None, the node pair does not exist.
///     Otherwise, the Some contains the graph resulting from applying
///     <paramref name="f" /> to the records of nodes
///     <paramref name="x" /> and <paramref name="y" /> in
///     <paramref name="graph" />.
/// </returns>
let mapNodePair
  (f : Set<OutEdge> -> Set<InEdge> -> (Set<OutEdge> * Set<InEdge>))
  (x : NodeID)
  (y : NodeID)
  (graph : Graph) =
    match (Map.tryFind x graph.Contents,
           Map.tryFind y graph.Contents) with
    | (Some (xv, xOut, xIn, xnk), Some (yv, yOut, yIn, ynk)) ->
        let xOut', yIn' = f xOut yIn

        // If x = y, we have to be careful to write all changes back.
        let contents' =
            graph.Contents
            |> if x = y
               then (Map.add x (xv, xOut', yIn', xnk))
               else (Map.add x (xv, xOut', xIn, xnk))
                     >> Map.add y (yv, yOut, yIn', ynk)

        Some { graph with Contents = contents' }
    | _ -> None

/// <summary>
///     Adds an edge to the graph.
/// </summary>
/// <param name="src">
///     The source node.
/// </param>
/// <param name="dest">
///     The destination node.
/// </param>
/// <param name="name">
///     A name for the parameter.
///     This must be unique.
/// </param>
/// <param name="p">
///     The payload carried by the edge.
/// </param>
/// <param name="graph">
///     The graph to extend.
/// </param>
/// <returns>
///     An Option: None if either <paramref name="src" /> or
///     <paramref name="dest" /> point out of the graph.
///     Else, the graph resulting from adding an edge from
///     <paramref name="src" /> to <paramref name="dest" />, with payload
///     <paramref name="p"/>, to <paramref name="graph"/>.
/// </returns>
let mkEdgeBetween
  (src : NodeID)
  (dest : NodeID)
  (name : EdgeID)
  (p : EdgePayload)
  (graph : Graph)
  : Graph option =
    // TODO(CaptainHayashi): signal an error if name is taken.
    mapNodePair
        (fun srcOut destIn ->
             // An edge is recorded as an out in src, and in in dest.

             let srcOut' = Set.add { Name = name
                                     Dest = dest
                                     Payload = p }
                                   srcOut

             let destIn' = Set.add { Name = name
                                     Src = src
                                     Payload = p }
                                    destIn

             (srcOut', destIn'))
        src
        dest
        graph


/// <summary>
///     Removes all edges with the given source and destination,
///     whose name satisfies a predicate.
/// </summary>
/// <param name="src">
///     The source node.
/// </param>
/// <param name="dest">
///     The destination node.
/// </param>
/// <param name="pred">
///     A predicate that must hold true on the edge's name for it to
///     be removed.
/// </param>
/// <param name="_arg1">
///     The <c>Graph</c> to prune.
/// </param>
/// <returns>
///     An Option: None if either <paramref name="src" /> or
///     <paramref name="dest" /> point out of the graph.
///     Else, contains <paramref name="_arg1" /> with all edges
///     between <param name="src" /> and <param name="dest" />
///     removed.  If either or both edges do not exist, the graph
///     is not changed.
/// </returns>
let rmEdgesBetween (src : NodeID) (dest : NodeID) (pred : EdgeID -> bool)
  : Graph -> Graph option =
    (* The result will be a well-formed graph, because it cannot
     * create dangling edges.
     *)
    mapNodePair
        (fun srcOut destIn ->
             // We need to delete the out entry in src going to dest...
             let srcOut' = Set.filter (fun { Dest = d ; Name = n } ->
                                       not (d = dest && pred n)) srcOut
             // ...and the in entry in dest coming from src.
             let destIn' = Set.filter (fun { Src = s ; Name = n } ->
                                       not (s = src && pred n)) destIn

             (srcOut', destIn'))
        src
        dest

/// <summary>
///     Removes a node, if it has no edges left.
/// </summary>
/// <param name="node">
///     The name of the node to remove.
/// </param>
/// <param name="graph">
///     The graph to prune.
/// </param>
/// <returns>
///     An Option: None if <paramref name="node" /> does not exist or has
///     edges pointing into or out of it.
///     Else, the graph resulting from
///     removing <paramref name="node" /> from <paramref name="graph" />.
/// </returns>
let rmNode (node : NodeID) (graph : Graph) : Graph option =
    // TODO(CaptainHayashi): Chessie-ise this and the other functions?
    match Map.tryFind node graph.Contents with
    | Some (_, outE, inE, _) when Set.isEmpty outE && Set.isEmpty inE ->
        Some { graph with Contents = Map.remove node graph.Contents }
    | _ -> None

(*
 * Graph queries
 *)

/// <summary>
///     Maps a function over all of the edges of a graph.
/// </summary>
/// <param name="f">
///     The function to map, which will receive the edges as
///     <c>FullEdge</c>s.
/// </param>
/// <param name="graph">
///     A graph, the edges of which we will be mapping.
/// </param>
/// <typeparam name="result">
///     The result of each iteration of the map.
/// </typeparam>
/// <returns>
///     A sequence collecting the results of the map.
/// </returns>
let mapEdges (f : FullEdge -> 'result) (graph : Graph) : 'result seq =
    let m = graph.Contents

    m
    |> Map.toSeq
    |> Seq.collect
           (fun (srcName, (srcView, outEdges, inEdges, _)) ->
                Seq.map
                    (fun { OutEdge.Name = edgeName
                           OutEdge.Payload = p
                           OutEdge.Dest = destName } ->
                         let dv, _, _, _ = m.[destName]
                         f { FullEdge.Name = edgeName
                             FullEdge.Payload = p
                             FullEdge.SrcName = srcName
                             FullEdge.SrcView = srcView
                             FullEdge.DestName = destName
                             FullEdge.DestView = dv } )
                    outEdges)

/// <summary>
///     Returns true if a node is present and has the given view.
/// </summary>
/// <param name="nodeName">
///     The name of the node to look-up.
/// </param>
/// <param name="nodeView">
///     The expected view of the node to look-up.
/// </param>
/// <param name="graph">
///     The graph to query.
/// </param>
/// <returns>
///     True if, and only if, <paramref name="nodeName" /> exists in
///     <paramref name="graph" /> and its view is structurally equal
///     to <paramref name="nodeView" />.
/// </returns>
let nodeHasView
  (nodeName : NodeID) (nodeView : GraphView) (graph : Graph)
  : bool =
    match (Map.tryFind nodeName graph.Contents) with
    | Some (InnerView v, _, _, _) -> v = nodeView
    | _ -> false

(*
 * Axiomatisation
 *)

/// <summary>
///     Returns the axioms characterising a graph.
/// </summary>
/// <param name="g">
///     The graph whose axioms are to be given.
/// </param>
/// <returns>
///     The command edges of <paramref name="g" />, as name-edge pairs.
///     This is wrapped in a Chessie result over <c>Error</c>.
/// </returns>
let axiomatiseGraph (g : Graph) : (string * Axiom<GraphView, Command>) seq =
    let edgeseqs =
        mapEdges
            (fun { Name = n; SrcView = s ; DestView = t ; Payload = p } ->
                match p with
                | ECommand c ->
                    Seq.singleton
                        (n, { Pre = match s with InnerView v -> v
                              Post = match t with InnerView v -> v
                              Cmd = c } )
                | EMiracle -> Seq.empty)
            g
    Seq.concat edgeseqs

/// <summary>
///     Converts a list of control-flow graphs into a list of axioms.
///
///     <para>
///         Each axiom represents an edge in a control-flow graph.
///     </para>
/// </summary>
/// <param name="_arg1">
///     The sequence of graphs to axiomatise.
///     Such graphs typically represent one method.
/// </param>
/// <returns>
///     A map of axioms characterising <paramref name="_arg1" />.
/// </returns>
let axiomatiseGraphs
  : Map<string, Graph> -> Map<string, Axiom<GraphView, Command>> =
    // The map key is redundant, as we already have it inside the
    // graph iself.
    Map.toSeq
    >> Seq.map (snd >> axiomatiseGraph)
    >> Seq.concat
    >> Map.ofSeq

/// <summary>
///     Converts a CFG-based model into an axiom-based model.
///
///     <para>
///         Each axiom represents an edge in a control-flow graph.
///     </para>
/// </summary>
/// <param name="model">
///     The model to axiomatise.
/// </param>
/// <returns>
///     An axiom-based model equivalent to <paramref name="model" />,
///     wrapped in a Chessie result.
/// </returns>
let axiomatise
  (model : Model<Graph, _>)
  : Model<Axiom<GraphView, Command>, _> =
    withAxioms (axiomatiseGraphs model.Axioms) model


/// <summary>
///     Pretty printers for control-flow graphs.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    open Starling.Core.Model.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Axiom.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.GuardedView.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty

    /// <summary>
    ///     Pretty-prints a <see cref="GraphView"/>.
    /// </summary>
    /// <param name="view">The <see cref="GraphView"/> to print.</param>
    /// <returns>
    ///     The resulting <see cref="Doc"/> from <paramref name="view"/>.
    /// </returns>
    let printGraphView (view : GraphView) : Doc =
        printGView (printSym printVar) view

    /// <summary>
    ///     A configuration for graph pretty-printing.
    /// </summary>
    type Config =
        | /// <summary>
          ///     Use shapes and colours to differentiate node and edge
          ///     kinds, making the graph human-readable.
          /// </summary>
          Fancy
        | /// <summary>
          ///     Use verbose labels to differentiate node and edge
          ///     kinds, making the graph machine-readable.
          /// </summary>
          Plain
        /// <summary>
        ///     Prints an associated list of GraphViz directives.
        /// </summary>
        /// <param name="assoc">The associated list.</param>
        /// <returns>A pretty-printer command for the directive list.</returns>
        member private cfg.PrintDirectiveList
          (assoc : (string * Doc) list) : Doc =
            let pPair (k, v) = String k <+> String "=" <+> v
            squared (hsep (List.map pPair assoc))

        /// <summary>
        ///     Prints a plain GraphViz label directive.
        /// </summary>
        /// <param name="labelCmd">
        ///     The pretty-printer command to use as the label.
        /// </param>
        /// <returns>
        ///     A pretty-printer command representing
        ///     [label = "<paramref name="labelCmd" />"].
        /// </returns>
        member private cfg.PrintPlainLabel (labelCmd : Doc) : Doc =
            cfg.PrintDirectiveList
                [ ("label", ssurround "\"" "\"" labelCmd) ]

        /// <summary>
        ///     Prints a view in a fancy manner.
        /// </summary>
        /// <param name="id">The ID of the view to print.</param>
        /// <param name="view">
        ///     The <c>GraphViewExpr</c> to print.
        /// </param>
        /// <param name="nk">
        ///     The kind of the node.
        /// </param>
        /// <returns>
        ///     A pretty-printer <c>Doc</c> representing the view.
        /// </returns>
        member private cfg.PrintFancyView
          (id : NodeID) (view : GraphViewExpr) (nk : NodeKind) : Doc =
            let hrow content =
                ssurround "<TR><TD COLSPAN=\"3\">" "</TD></TR>" (String content)

            let v, comment =
                match view with
                | Mandatory v -> Multiset.toFlatSeq v, Nop 
                | Advisory v -> Multiset.toFlatSeq v, hrow "(Advisory)"

            let funcToRow (v : GFunc<Sym<Var>>) =
                ssurround "<TR>" "</TR>"
                    ((ssurround "<TD>" "</TD>" 
                        (printBoolExpr (printSym printVar) v.Cond))
                     <->
                     (ssurround "<TD>" "</TD>" (printSVFunc v.Item)))

            let vrows = Seq.map funcToRow v
            let header = hrow id <-> comment

            // Differentiate nodekinds by colour.
            let colour =
                match nk with
                | Normal -> "beige"
                | Entry -> "coral"
                | Exit -> "aquamarine"
                | EntryExit -> "cornflowerblue"

            Surround
                (String "<TABLE CELLSPACING=\"0\" BGCOLOR=\"" <-> String colour <-> String "\">",
                 header <-> hsep vrows,
                 String "</TABLE>")


        /// <summary>
        ///     Prints a node.
        /// </summary>
        /// <param name="id">
        ///     The unique ID of the node.
        /// </param>
        /// <param name="view">
        ///     The <c>GraphViewExpr</c> contained in the node.
        /// </param>
        /// <param name="nk">
        ///     The kind of the node.
        /// </param>
        /// <returns>
        ///     A pretty-printer <c>Command</c> representing the node.
        /// </returns>
        member private cfg.PrintNode
          (id : NodeID)
          (view : GraphViewExpr)
          (nk : NodeKind)
          : Doc =
            let nodeRhs =
                match cfg with
                | Plain ->
                    let elements =
                        seq {
                           yield String id
                           yield printViewExpr printGraphView view
                           match nk with
                           | Normal -> ()
                           | Entry -> yield String "(Entry)"
                           | Exit -> yield String "(Exit)"
                           | EntryExit -> yield String "(EntryExit)"
                        }
                    cfg.PrintPlainLabel (colonSep elements)
                | Fancy ->
                    cfg.PrintDirectiveList
                        [ ("label", 
                            ssurround "<" ">" (cfg.PrintFancyView id view nk))
                          ("shape", String "plain") ]
            withSemi (String id <+> nodeRhs)

        /// <summary>
        ///     Prints the properties list of a command edge.
        /// </summary>
        /// <param name="id">The name of the edge.</param>
        /// <param name="cmd">The command of the edge.</param>
        /// <returns>
        ///     A pretty-printer <c>Doc</c> representing the edge properties.
        /// </returns>
        member private cfg.PrintCommandEdgeRhs (id : EdgeID) (cmd : Command) =
            match cfg with
            | Plain ->
                cfg.PrintPlainLabel (colonSep [ String id; printCommand cmd ])
            | Fancy ->
                // Colour certain commands based on their nature.
                let colour =
                    match cmd with
                    | Starling.Core.Command.Queries.Assume _ -> "blue"
                    | Starling.Core.Command.Queries.NopCmd _ -> "green"
                    | _ -> "black"

                cfg.PrintDirectiveList
                    [ ("label",
                       ssurround "<" ">"
                        (hsep
                            [ String id
                              String "<BR/>"
                              printCommand cmd ]))
                      ("color", String colour) ]

        /// <summary>
        ///     Prints the properties list of a miracle edge.
        /// </summary>
        /// <param name="id">The name of the edge.</param>
        /// <returns>
        ///     A pretty-printer <c>Doc</c> representing the edge properties.
        /// </returns>
        member private cfg.PrintMiracleEdgeRhs (id : EdgeID) =
            match cfg with
            | Plain ->
                cfg.PrintPlainLabel (colonSep [ String id; String "(miracle)" ])
            | Fancy ->
                cfg.PrintDirectiveList
                    [ ("label",
                       ssurround "<" ">" (String id))
                      ("style", String "dotted")
                      ("color", String "gray") ]

        /// <summary>
        ///     Prints an edge.
        /// </summary>
        /// <param name="id">
        ///     The unique ID of the node.
        /// </param>
        /// <param name="e">
        ///     The <c>Edge</c> to print.
        /// </param>
        /// <returns>
        ///     A pretty-printer <c>Command</c> representing
        ///     <paramref name="e" />.
        /// </returns>
        member cfg.PrintEdge (id : EdgeID) (e : Edge) : Doc =
            let s, t, rhs =
                match e with
                | CommandEdge { Pre = s; Post = t; Cmd = cmd } ->
                    s, t, cfg.PrintCommandEdgeRhs id cmd
                | MiracleEdge (s, t) ->
                    s, t, cfg.PrintMiracleEdgeRhs id

            withSemi
                (String s <+> String "->" <+> String t <+> rhs)

        /// <summary>
        ///     Prints a <c>Subgraph</c>.
        /// </summary>
        /// <param name="s">The subgraph to print.</param>
        /// <returns>
        ///     A pretty-printer <c>Command</c> that prints
        ///     <paramref name="_arg1" />.
        /// </returns>
        member cfg.PrintSubgraph (s : Subgraph) : Doc =
            let docs =
                seq {
                    for (id, (node, kind)) in Map.toSeq s.Nodes do
                        yield cfg.PrintNode id node kind
                    for (id, edge) in Map.toSeq s.Edges do
                        yield cfg.PrintEdge id edge
                }
            braced (ivsep docs)

    /// <summary>
    ///     Prints a <c>Graph</c>.
    ///
    ///     <para>
    ///         This pretty printer should create a dot-compatible digraph.
    ///     </para>
    /// </summary>
    /// <param name="cfg">Configuration for the graph pretty-printer.</param>
    /// <param name="graph">
    ///     The graph to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> that prints
    ///     <paramref name="graph" />.
    /// </returns>
    let printGraph (cfg : Config) (graph : Graph) : Doc =
        hsep [ String "digraph"
               String graph.Name

               // TODO(CaptainHayashi): don't convert here?
               graph |> toSubgraph |> cfg.PrintSubgraph ]

    /// <summary>
    ///     Pretty-prints graph construction errors.
    /// </summary>
    /// <param name="err">The graph error to print.</param>
    /// <returns>
    ///     A pretty-printer command that prints <paramref name="err" />.
    /// </returns>
    let rec printError (err : Error) : Doc =
        match err with
        | EdgeOutOfBounds (edgeID, edge) ->
            colonSep
                [ String "edge out of bounds"; Plain.PrintEdge edgeID edge ]
        | DuplicateNode node ->
            colonSep [ String "node duplicated"; String node ]
        | DuplicateEdge edge ->
            colonSep [ String "edge duplicated"; String edge ]
        | Traversal err -> Starling.Core.Traversal.Pretty.printTraversalError printError err
