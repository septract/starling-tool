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

open Starling.Utils
open Starling.Core.Model
open Starling.Core.Axiom


/// <summary>
///     Pretty printers for control-flow graphs.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     Type synonym for graph edges.
    ///
    ///     <para>
    ///         Graph edges are axioms, in that they directly correspond to
    ///         Hoare triples.
    ///     </para>
    /// </summary>
    type Edge = Axiom<string, Command>

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
            Nodes: Map<string, GView>

            /// <summary>
            ///     Set of edges in the control-flow graph.
            /// </summary>
            Edges: Map<string, Edge>
        }

    /// <summary>
    ///     An in edge in a standalone control-flow graph.
    /// </summary>
    type InEdge =
        { /// <summary>
          ///      The name of the edge.
          /// </summary>
          Name : string
          /// <summary>
          ///      The source of this edge.
          /// </summary>
          Src : string
          /// <summary>
          ///      The command this edge represents.
          /// </summary>
          Command : Command }

    /// <summary>
    ///     An out edge in a standalone control-flow graph.
    /// </summary>
    type OutEdge =
        { /// <summary>
          ///      The name of the edge.
          /// </summary>
          Name : string
          /// <summary>
          ///      The destination of this edge.
          /// </summary>
          Dest : string
          /// <summary>
          ///      The command this edge represents.
          /// </summary>
          Command : Command }

    /// <summary>
    ///     A fully resolved edge, containing views.
    /// </summary>
    type FullEdge =
        { /// <summary>
          ///     The name of the edge.
          /// </summary>
          Name : string
          /// <summary>
          ///     The name of the source node.
          /// </summary>
          SrcName : string
          /// <summary>
          ///     The view of the source node.
          /// </summary>
          SrcView : GView
          /// <summary>
          ///     The name of the destination node.
          /// </summary>
          DestName : string
          /// <summary>
          ///     The view of the destination node.
          /// </summary>
          DestView : GView
          /// <summary>
          ///      The command this edge represents.
          /// </summary>
          Command : Command }

    /// <summary>
    ///     A standalone control-flow graph.
    ///
    ///     <para>
    ///         Control-flow graphs use an adjacency list format.
    ///     </para>
    /// </summary>
    type Graph = { /// <summary>
                   ///     The name of the graph.
                   /// </summary>
                   Name : string
                   /// <summary>
                   ///     The contents of the graph.
                   /// </summary>
                   Contents : Map<string, (GView * Set<OutEdge>
                                                 * Set<InEdge>)> }

    /// <summary>
    ///     Type of Chessie errors for CFG actions.
    /// </summary>
    type Error =
        /// <summary>
        ///     The given edge has an invalid node index.
        /// </summary>
        | EdgeOutOfBounds of Edge
        /// <summary>
        ///     The given node was duplicated when trying to merge graphs.
        /// </summary>
        | DuplicateNode of id: string
        /// <summary>
        ///     The given edge was duplicated when trying to merge graphs.
        /// </summary>
        | DuplicateEdge of id: string


/// <summary>
///     Creates a single <c>Edge</c>.
/// </summary>
/// <param name="_arg1">
///     The source view.
/// </param>
/// <param name="_arg2">
///     The command making up the edge.
/// </param>
/// <param name="_arg3">
///     The target view.
/// </param>
/// <returns>
///     An <c>Edge</c> with the above properties.
/// </returns>
let edge = axiom

/// <summary>
///     Converts a <c>Graph</c> to a <c>Subgraph</c>.
/// </summary>
/// <param name="graph" />
///     The graph to convert to a subgraph.
/// </param>
/// <returns>
///     A <c>Subgraph</c> giving the same nodes and edges as
///     <paramref name="graph" />.
/// </returns>
let toSubgraph graph =
    { Nodes =
          graph.Contents
          |> Map.toSeq
          |> Seq.map (fun (nodeName, (nodeView, _, _)) -> (nodeName, nodeView))
          |> Map.ofSeq
      Edges =
          graph.Contents
          |> Map.toSeq
          |> Seq.map
                 (fun (fromName, (_, outEdges, _)) ->
                      Seq.map
                          (fun { Name = n; Dest = toName; Command = cmd } ->
                               (n, edge fromName cmd toName))
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
let graph name sg =
    // Are any of the node indices out of bounds?
    match (Map.filter
               (fun _ {Pre = s; Post = t} ->
                    not (Map.containsKey s sg.Nodes &&
                         Map.containsKey t sg.Nodes))
               sg.Edges) |> Map.toList with
    | [] ->
        sg.Nodes
        |> Map.map
               (fun nodeName nodeView ->
                    let outEdges =
                        sg.Edges
                        |> Map.toSeq
                        |> Seq.choose
                               (fun (edgeName, { Pre = src
                                                 Post = dst
                                                 Cmd = cmd }) ->
                                if src = nodeName
                                then (Some { OutEdge.Name = edgeName
                                             OutEdge.Command = cmd
                                             OutEdge.Dest = dst })
                                else None)
                         |> Set.ofSeq
                    let inEdges =
                        sg.Edges
                        |> Map.toSeq
                        |> Seq.choose
                               (fun (edgeName, { Pre = src
                                                 Post = dst
                                                 Cmd = cmd }) ->
                                if dst = nodeName
                                then (Some { InEdge.Name = edgeName
                                             InEdge.Command = cmd
                                             InEdge.Src = src })
                                else None)
                         |> Set.ofSeq
                    (nodeView, outEdges, inEdges))
        |> fun m -> { Name = name ; Contents = m }
        |> ok
    | xs -> xs |> List.map (snd >> EdgeOutOfBounds) |> Bad

/// <summary>
///    Combines two subgraphs.
/// </summary>
/// <param name="_arg1">
///    The first graph to combine.
/// </param>
/// <param name="_arg2"
///    The second graph to combine.
/// </param>
/// <returns>
///     A <c>Subgraph</c>, wrapped in a Chessie result over <c>Error</c>.
///     If the two graphs do not contain duplicate
///     nodes, then the result will be <c>ok</c>.
///     The graph will contain the nodes and edges from <paramref
///     name="_arg1" /> and <paramref name="_arg2" />.
/// </returns>
let combine { Nodes = ans ; Edges = aes }
            { Nodes = bns ; Edges = bes } =
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
/// <param name="source">
///     The node to delete in the unification.
/// </param>
/// <param name="target">
///     The node to keep in the unification.
/// </param>
/// <param name="graph">
///     The subgraph to transform.
/// </param>
/// <returns>
///     The graph that is <paramref name="graph" /> but with
///     <paramref name="source" /> deleted, and all edges starting and ending
///     at it redirected to <paramref name="target" />.
/// </returns>
/// <remarks>
///     <para>
///         If <c>source = target</c>, or either of the nodes do not exist,
///         <paramref name="graph" /> is returned unchanged.
///     </para>
/// </remarks>
let unify source target graph =
    if (source = target)
       || (not (Map.containsKey source graph.Contents))
       || (not (Map.containsKey target graph.Contents))
    then graph
    else
        // Pull out the source's entry, ready to append later.
        let _, srcOut, srcIn = graph.Contents.[source]

        let swapNode = function
                       | n when n = source -> target
                       | n -> n
        let swapIn o = { o with Src = swapNode o.Src }
        let swapOut o = { o with Dest = swapNode o.Dest }

        (* Remove a node if it is source;
         * otherwise, inspect its nodes for source, and rewrite them
         * to target.  If the node is target, add in the source edges.
         *)
        let unifyStep (name, (view, outEdges, inEdges)) =
            if name = source
            then None
            else
                let newOut =
                    outEdges
                    |> Set.map swapOut
                    |> if name = target then Set.union srcOut else id
                let newIn =
                    inEdges
                    |> Set.map swapIn
                    |> if name = target then Set.union srcIn else id

                Some (name, (view, newOut, newIn))

        let contents =
            graph.Contents
            |> Map.toSeq
            |> Seq.choose unifyStep
            |> Map.ofSeq

        { graph with Contents = contents }


/// <summary>
///     Performs an operation on two nodes in a graph.
/// </summary>
/// <param name="f">
///     The function to apply.
///     This receives two parameters: the adjacency list records
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
///     The graph resulting from applying <paramref name="f" /> to
///     the records of nodes <paramref name="x" /> and
///     <paramref name="y" /> in <paramref name="graph" />.
/// </returns>
let mapNodePair f x y graph =
    match (Map.tryFind x graph.Contents,
           Map.tryFind y graph.Contents) with
    | (Some xRecord, Some yRecord) ->
        let xRecord', yRecord' = f xRecord yRecord

        let contents' =
            graph.Contents
            |> Map.add x xRecord'
            |> Map.add y yRecord'

        { graph with Contents = contents' }
    | _ -> graph

/// <summary>
///     Adds an edge to the graph.
/// </summary>
/// <param name="name">
///     A name for the parameter.
///     This must be unique.
/// </param>
/// <param name="src">
///     The source node.
/// </param>
/// <param name="dest">
///     The destination node.
/// </param>
/// <param name="cmd">
///     The command occurring on the edge.
/// </param>
/// <param name="graph">
///     The graph to extend.
/// </param>
/// <returns>
///     The graph resulting from adding an edge from
///     <paramref name="src" /> to <paramref name="dest" />, with command
///     <paramref name="cmd"/>, to <paramref name="graph"/>.
///
///     <para>
///         This is a no-operation if either <paramref name="src" />
///         or <paramref name="dest" /> point outside of the graph.
///     </para>
/// </returns>
let mkEdgeBetween name src dest cmd graph =
    // TODO(CaptainHayashi): signal an error if name is taken.
    mapNodePair
        (fun (srcView, srcOut, srcIn) (destView, destOut, destIn) ->
             // An edge is recorded as an out in src, and in in dest.

             let srcOut' = Set.add { Name = name
                                     Dest = dest
                                     Command = cmd }
                                   srcOut

             let destIn' = Set.add { Name = name
                                     Src = src
                                     Command = cmd }
                                    destIn

             ((srcView, srcOut', srcIn),
              (destView, destOut, destIn')))
        src
        dest
        graph


/// <summary>
///     Removes all edges with the given source and destination.
/// </summary>
/// <param name="src">
///     The source node.
/// </param>
/// <param name="dest">
///     The destination node.
/// </param>
/// <param name="_arg1">
///     The <c>Graph</c> to prune.
/// </param>
/// <returns>
///     The equivalent of <paramref name="_arg1" /> with all edges
///     between <param name="src" /> and <param name="dest" />
///     removed.  If either or both edges do not exist, the graph
///     is not changed.
/// </returns>
let rmEdgesBetween src dest =
    (* The result will be a well-formed graph, because it cannot
     * create dangling edges.
     *)
    mapNodePair
        (fun (srcView, srcOut, srcIn) (destView, destOut, destIn) ->
             // We need to delete the out entry in src going to dest...
             let srcOut' = Set.filter (fun { Dest = d } -> d <> dest) srcOut
             // ...and the in entry in dest coming from src.
             let destIn' = Set.filter (fun { Src = s } -> s <> src) destIn

             ((srcView, srcOut', srcIn),
              (destView, destOut, destIn')))
        src
        dest

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
/// <returns>
///     A sequence collecting the results of the map.
/// </returns>
let mapEdges f graph =
    let m = graph.Contents

    m
    |> Map.toSeq
    |> Seq.map
           (fun (srcName, (srcView, outEdges, inEdges)) ->
                Seq.map
                    (fun { OutEdge.Name = edgeName
                           OutEdge.Command = cmd
                           OutEdge.Dest = destName } ->
                         let dv, _, _ = m.[destName]
                         f { FullEdge.Name = edgeName
                             FullEdge.Command = cmd
                             FullEdge.SrcName = srcName
                             FullEdge.SrcView = srcView
                             FullEdge.DestName = destName
                             FullEdge.DestView = dv } )
                    outEdges)
    |> Seq.concat


(*
 * Axiomatisation
 *)

/// <summary>
///     Returns the axioms characterising a graph.
/// </summary>
/// <param name="_arg1">
///     The graph whose axioms are to be given.
/// </param>
/// <returns>
///     The edges of <paramref name="_arg1" />, as name-edge pairs.
///     This is wrapped in a Chessie result over <c>Error</c>.
/// </returns>
let axiomatiseGraph =
    mapEdges
           (fun { Name = n; SrcView = s ; DestView = t ; Command = c } ->
                (n, { Pre = s ; Post = t ; Cmd = c } ))

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
let axiomatiseGraphs =
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
let axiomatise model =
    withAxioms (axiomatiseGraphs model.Axioms) model


/// <summary>
///     Pretty printers for control-flow graphs.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    open Starling.Core.Model.Pretty
    open Starling.Core.Axiom.Pretty


    /// <summary>
    ///     Prints a GraphViz label directive.
    /// </summary>
    /// <param name="labelCmd">
    ///     The pretty-printer command to use as the label.
    /// </param.
    /// <returns>
    ///     A pretty-printer command representing
    ///     [label = "<paramref name="labelCmd" />"].
    /// </returns>
    let printLabel labelCmd =
        [ String "label"
          String "="
          labelCmd |> ssurround "\"" "\"" ]
        |> hsep |> squared

    /// <summary>
    ///     Prints a node.
    /// </summary>
    /// <param name="id">
    ///     The unique ID of the node.
    /// </param>
    /// <param name="view">
    ///     The <c>GView</c> contained in the node.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> representing the node.
    /// </returns>
    let printNode id view =
        hsep [ id |> String
               [ id |> String
                 view |> printGView ] |> colonSep |> printLabel ]
        |> withSemi

    /// <summary>
    ///     Prints an edge.
    /// </summary>
    /// <param name="id">
    ///     The unique ID of the node.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>Edge</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> representing
    ///     <paramref name="_arg1" />.
    /// </returns>
    let printEdge id { Pre = s; Post = t; Cmd = cmd } =
        hsep [ s |> String
               String "->"
               t |> String
               [ id |> String
                 cmd |> printCommand ] |> colonSep |> printLabel ]
        |> withSemi

    /// <summary>
    ///     Prints a <c>Subgraph</c>.
    /// </summary>
    /// <param name="_arg1">
    ///     The subgraph to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> that prints
    ///     <paramref name="_arg1" />.
    /// </returns>
    let printSubgraph { Nodes = nodes ; Edges = edges } =
        Seq.append
            (nodes |> Map.toSeq |> Seq.map (uncurry printNode))
            (edges |> Map.toSeq |> Seq.map (uncurry printEdge))
        |> ivsep |> braced

    /// <summary>
    ///     Prints a <c>Graph</c>.
    ///
    ///     <para>
    ///         This pretty printer should create a dot-compatible digraph.
    ///     </para>
    /// </summary>
    /// <param name="graph">
    ///     The graph to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> that prints
    ///     <paramref name="graph" />.
    /// </returns>
    let printGraph graph =
        hsep [ String "digraph"
               String graph.Name


               // TODO(CaptainHayashi): don't convert here?
               graph |> toSubgraph |> printSubgraph ]

    /// <summary>
    ///     Pretty-prints graph construction errors.
    /// </summary>
    /// <param name="_arg1">
    ///     The graph error to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command that prints
    ///     <paramref name="_arg1" />.
    /// </returns>
    let printError =
        function
        | EdgeOutOfBounds edge ->
            colonSep
                [ String "edge out of bounds: "
                  printAxiom printCommand
                             (fun x -> String (x.ToString()))
                             edge ]
        | DuplicateNode node ->
            colonSep [ String "node duplicated: "; String node ]
        | DuplicateEdge edge ->
            colonSep [ String "edge duplicated: "; String edge ]
