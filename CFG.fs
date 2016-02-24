/// <summary>
///     Types and helper functions for Starling control-flow graphs.
///
///     <para>
///         Starling CFGs contain one node per view assertion, and one edge per
///         command.
///     </para>
/// </summary>
module Starling.CFG

open Chessie.ErrorHandling
open Starling.Model


(*
 * Types
 *)

/// <summary>
///     Type of edges in a control-flow graph.
///
///     <para>
///         Each edge is stored as an edge from a source node
///         to a target node.
///     </para>
/// </summary>
/// <typeparam name="node" />
///     The type of node references in this edge: usually <c>int</c>
///     (referencing nodes by index) or <c>Node</c> (containing node
///     information inline).
/// </typeparam>
type Edge<'node> =
    {
        /// <summary>
        ///     The source for this edge.
        /// </summary>
        Source: 'node

        /// <summary>
        ///     The target for this edge.
        /// </summary>
        Target: 'node

        /// <summary>
        ///     The command, as a <c>VFunc</c>, to run on this edge.
        /// </summary>
        Cmd: VFunc
    }

/// <summary>
///     The container for a control-flow graph.
/// </summary>
type Graph =
    {
        /// <summary>
        ///     Set of nodes in the control-flow graph.
        /// </summary>
        Nodes: Map<int, View>

        /// <summary>
        ///     Set of edges in the control-flow graph.
        /// </summary>
        Edges: Edge<int> list
    }

/// <summary>
///     Type of Chessie errors for CFG actions.
/// </summary>
type Error =
    /// <summary>
    ///     The given edge has an invalid node index.
    /// </summary>
    | EdgeOutOfBounds of Edge<int>


(*
 * Helper functions
 *)

/// <summary>
///     Attempts to create a new <c>Graph</c>.
/// </summary>
/// <param name="nodes">
///     The map of nodes in the graph.
/// </param>
/// <param name="edges">
///     The sequence of edges in the graph.
/// </param>
/// <returns>
///     A <c>Graph option</c>, which is <c>Some</c> if the edges are
///     valid (reference indices in <paramref name="nodes" />, and
///     <c>None</c> otherwise.)
/// </returns>
let graph nodes edges =
    let edgesL = Seq.toList edges

    // Are any of the node indices out of bounds?
    match (List.filter
               (fun {Source = s; Target = t} ->
                    not (Map.containsKey s nodes &&
                         Map.containsKey t nodes))     
               edgesL) with
    | [] -> { Nodes = nodes; Edges = edgesL } |> ok
    | xs -> xs |> Seq.map EdgeOutOfBounds |> fail

/// <summary>
///     Folds <paramref name="f" /> over all edges in a graph.
/// </summary>
/// <typeparam name="state">
///     The type of the state built by folding.
/// </param>
/// <param name="f">
///     The function to fold over all graph edges, taking a source
///     <c>View</c>, a <c>VFunc</c> representing a command, and a
///     target <c>View</c>.  It should return a <c>'state</c>.
/// </param>
/// <param name="init">
///     The initial state to send to <paramref name="f" />.
/// </param>
/// <param name="_arg1">
///     The graph whose edges are to be folded over.
/// </param>
/// <returns>
///     The result of folding <paramref name="f" /> over <paramref
///     name="init" /> and the graph <paramref name="_arg1" />.
///     This is wrapped in a Chessie result over <c>Error</c>.
/// </returns>
let fold f init { Nodes = nodes; Edges = edges } =
    edges
    |> Seq.map
           (fun { Source = s; Target = t; Cmd = c } ->
                match (Map.tryFind s nodes, Map.tryFind t nodes) with
                | Some sn, Some tn -> ok { Source = sn; Target = tn; Cmd = c }
                | _ -> { Source = s; Target = t; Cmd = c } |> EdgeOutOfBounds |> fail)
    |> collect
    |> lift (Seq.fold f init)
