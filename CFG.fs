/// <summary>
///     Types and helper functions for Starling control-flow graphs.
///
///     <para>
///         Starling CFGs contain one node per view assertion, and one edge per
///         command.
///     </para>
/// </summary>
namespace Starling.CFG

open Starling.Model

/// <summary>
///     Type of edges in a control-flow graph.
///
///     <para>
///         Each edge is stored as a multi-edge from a list of source nodes
///         to a list of target nodes, where the lists represent parallel
///         fan-in and fan-out respectively.
///         The conjunction of all source views must entail the conjunction
///         of all target views.
///     </para>
/// </summary>
type Edge =
    {
        /// <summary>
        ///     The list of parallel sources for this edge.
        /// </summary>
        From: int list

        /// <summary>
        ///     The list of parallel targets for this edge.
        /// </summary>
        To: int list

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
        Nodes: View[]

        /// <summary>
        ///     Set of edges in the control-flow graph.
        /// </summary>
        Edges: Edge list
    }
