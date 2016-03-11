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
    type Edge = Axiom<string, VFunc>

    /// <summary>
    ///     The container for a partial control-flow graph.
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
    ///     The summary for a standalone control-flow graph.
    /// </summary>
    type Graph =
        { /// <summary>
          ///     The name of the graph.
          /// </summary>
          Name: string
          /// <summary>
          ///     The contents of the graph.
          /// </summary>
          Contents: Subgraph }

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
    let printEdge id { Pre = s; Post = t; Cmd = vf } =
        hsep [ s |> String
               String "->"
               t |> String
               [ id |> String
                 vf |> printVFunc ] |> colonSep |> printLabel ]
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
    /// <param name="_arg1">
    ///     The graph to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> that prints
    ///     <paramref name="_arg1" />.
    /// </returns>
    let printGraph { Name = name; Contents = sg } =
        hsep [ String "digraph"
               String name
               sg |> printSubgraph ]

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
                  printPAxiom (fun x -> String (x.ToString())) edge ]
        | DuplicateNode node ->
            colonSep [ String "node duplicated: "; String node ]
        | DuplicateEdge edge ->
            colonSep [ String "edge duplicated: "; String edge ]


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
///     Attempts to create a new <c>Graph</c> with no node checking.
/// </summary>
/// <param name="nodes">
///     The map of nodes in the graph.
/// </param>
/// <param name="edges">
///     The sequence of edges in the graph.
/// </param>
/// <returns>
///     A <c>Graph</c>, wrapped in a Chessie result over <c>Error</c>.
///     Currently, there are no possible errors.
/// </returns>
let subgraph nodes edges =
    { Nodes = nodes; Edges = edges } |> ok

/// <summary>
///     Checks that a subgraph is a standalone graph.
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
    | [] -> { Name = name; Contents = sg } |> ok
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
///     A <c>Graph</c>, wrapped in a Chessie result over <c>Error</c>.
///     If the two graphs do not contain duplicate
///     nodes, then the result will be <c>ok</c>.
///     The graph will contain the nodes and edges from <paramref
///     name="_arg1" /> and <paramref name="_arg2" />.
/// </returns>
let combine { Nodes = ans ; Edges = aes }
            { Nodes = bns; Edges = bes } =
    match (keyDuplicates ans bns |> Seq.toList,
           keyDuplicates aes bes |> Seq.toList) with
    | ([], []) -> subgraph (mapAppend ans bns) (mapAppend aes bes)
    | (xs, ys) -> List.append (xs |> List.map DuplicateNode)
                              (ys |> List.map DuplicateEdge)
                  |> Bad

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
let axiomatiseGraph { Name = name
                      Contents = { Nodes = nodes; Edges = edges } } =
    edges
    |> Map.toList
    |> Seq.map
           (fun (name, { Pre = s; Post = t; Cmd = c }) ->
                match (Map.tryFind s nodes, Map.tryFind t nodes) with
                | Some sn, Some tn ->
                    ok (name, { Pre = sn; Post = tn; Cmd = c })
                | _ ->
                    { Pre = s; Post = t; Cmd = c } |> EdgeOutOfBounds |> fail)
    |> collect

/// <summary>
///     Converts a list of control-flow graphs into a list of axioms.
///
///     <para>
///         Each axiom represents an edge in a control-flow graph.
///     </para>
/// </summary>
/// <param name="graphs">
///     The sequence of graphs to axiomatise.
///     Such graphs typically represent one method.
/// </param>
/// <returns>
///     A map of axioms characterising <paramref name="graphs" />,
///     wrapped in a Chessie result.
/// </returns>
let axiomatiseGraphs graphs =
    // The map key is redundant, as we already have it inside the
    // graph iself.
    graphs
    |> Map.toSeq
    |> Seq.map (snd >> axiomatiseGraph)
    |> collect
    |> lift (Seq.concat >> Map.ofSeq)

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
    lift (fun xs -> withAxioms xs model)
         (axiomatiseGraphs model.Axioms)


(*
 * Graph queries
 *)

/// <summary>
///     Returns all unique node pairs in the subgraph.
/// </summary>
/// <param name="subgraph" />
///     The subgraph to inspect.
/// </param>
/// <returns>
///     A sequence of every unique, irreflexive pair of node IDs in
///     the subgraph.  If (a, b) is in the sequence, (b, a) will not
///     be.  No guarantees are made as to ordering.
/// </returns>
let nodePairs subgraph =
    let allNodes = subgraph.Nodes |> Map.toSeq |> Seq.map fst

    allNodes
    |> Seq.mapi
       (fun i x ->
            Seq.map
                (mkPair x)
                (* The skip ensures uniqueness:
                 * if we're on index i, the first i nodes have been
                 * put in pairs, and the next node is us.
                 *)
                (Seq.skip (i + 1) allNodes))
    |> Seq.concat
