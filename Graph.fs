/// <summary>
///     Types and helper functions for Starling control-flow graphs.
///
///     <para>
///         Starling CFGs contain one node per view assertion, and one edge per
///         command.
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
    type Edge = Axiom<bigint, VFunc>

    /// <summary>
    ///     The container for a partial control-flow graph.
    /// </summary>
    type Subgraph =
        {
            /// <summary>
            ///     Set of nodes in the control-flow graph.
            /// </summary>
            Nodes: Map<bigint, GView>
    
            /// <summary>
            ///     Set of edges in the control-flow graph.
            /// </summary>
            Edges: Edge list
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
        | DuplicateNode of bigint


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
        hsep [ id |> sprintf "v%A" |> String
               view |> printGView |> printLabel ]
        |> withSemi

    /// <summary>
    ///     Prints an edge.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>Edge</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer <c>Command</c> representing
    ///     <paramref name="_arg1" />.
    /// </returns>
    let printEdge { Pre = s; Post = t; Cmd = vf } =
        hsep [ s |> sprintf "v%A" |> String
               String "->"
               t |> sprintf "v%A" |> String
               vf |> printVFunc |> printLabel ]
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
        List.append
            (nodes |> Map.toList |> List.map (uncurry printNode))
            (edges |> List.map printEdge)
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
            colonSep
                [ String "node duplicated: "
                  String (node.ToString()) ]


/// <summary>
///     Creates a single <c>Edge</c>.
/// </summary>
/// <param name="source">
///     The source view.
/// </param>
/// <param name="command">
///     The command making up the edge.
/// </param>
/// <param name="target">
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
    let edgesL = Seq.toList edges
    { Nodes = nodes; Edges = edgesL } |> ok

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
    match (List.filter
               (fun {Pre = s; Post = t} ->
                    not (Map.containsKey s sg.Nodes &&
                         Map.containsKey t sg.Nodes))
               sg.Edges) with
    | [] -> { Name = name; Contents = sg } |> ok
    | xs -> xs |> List.map EdgeOutOfBounds |> Bad

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
    match (keyDuplicates ans bns |> Seq.toList) with
    | [] -> subgraph (mapAppend ans bns) (Seq.append aes bes)
    | xs -> xs |> List.map DuplicateNode |> Bad

/// <summary>
///     Returns the axioms characterising a graph.
/// </summary>
/// <param name="_arg1">
///     The graph whose axioms are to be given.
/// </param>
/// <returns>
///     The edges of <paramref name="_arg1" />
///     This is wrapped in a Chessie result over <c>Error</c>.
/// </returns>
let axiomatiseGraph { Name = name; Contents = { Nodes = nodes; Edges = edges } } =
    edges
    |> Seq.map
           (fun { Pre = s; Post = t; Cmd = c } ->
                match (Map.tryFind s nodes, Map.tryFind t nodes) with
                | Some sn, Some tn -> ok { Pre = sn; Post = tn; Cmd = c }
                | _ -> { Pre = s; Post = t; Cmd = c } |> EdgeOutOfBounds |> fail)
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
///     A list of axioms characterising <paramref name="graph" />,
///     wrapped in a Chessie result.
/// </returns>
let axiomatiseGraphs (graphs: Graph seq)
                     : Result<Axiom<GView, VFunc> seq, Error> =
    graphs
    |> Seq.map axiomatiseGraph
    |> collect
    |> lift Seq.concat

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
    lift (fun xs -> withAxioms (Seq.toList xs) model)
         (axiomatiseGraphs model.Axioms)
