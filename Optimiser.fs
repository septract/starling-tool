/// <summary>
///     Graph and term optimisation.
///
///     <para>
///         This module contains two submodules: <c>Graph</c>, which optimises
///         control-flow graphs, and <c>Term</c>, which optimises proof terms.
///         Both intend to reduce the proof burden passed to the backends.
///     </para>
/// </summary>
module Starling.Optimiser

open System.Collections.Generic

open Chessie.ErrorHandling

open Starling.Core.TypeSystem
open Starling.Collections
open Starling.Utils
open Starling.Utils.Config
open Starling.Semantics
open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Command.Queries
open Starling.Core.Traversal
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal


/// <summary>
///     Types for the graph transformer.
/// </summary>
[<AutoOpen>]
module Types =
    open Starling.Core.Graph

    /// <summary>
    ///     A type of unification used with the <c>Unify</c> leg of
    ///     <see cref="Transform"/>.
    /// <summary>
    type UnifyMode =
        /// <summary>
        ///     Only unify if there are no edges between the two nodes to
        ///     unify.
        /// </summary>
        | OnlyIfNoConnections
        /// <summary>
        ///     Always unify, but make any connecting edges into cycles.
        /// </summary>
        | MakeConnectionsCycles
        /// <summary>
        ///     Always unify, and remove any connecting edges.
        /// </summary>
        | RemoveConnections

    /// <summary>
    ///     A graph transformer command.
    /// </summary>
    type Transform =
        /// <summary>
        ///    Remove the given node.
        ///    Abort transformation if the node does not exist, or has
        ///    dangling edges.
        /// </summary>
        | RmNode of node : string
        /// <summary>
        ///    Remove all edges from <c>src</c> to <c>dest</c>.
        ///    Abort transformation if the nodes do not exist.
        /// </summary>
        | RmAllEdgesBetween of src : string * dest : string
        /// <summary>
        ///    Remove the given in-edge leading into <c>node</c>.
        ///    Abort transformation if the edge doesn't make sense.
        /// </summary>
        | RmInEdge of edge : InEdge * dest : string
        /// <summary>
        ///    Remove the given out-edge leading out of <c>node</c>.
        ///    Abort transformation if the edge doesn't make sense.
        /// </summary>
        | RmOutEdge of src : string * edge : OutEdge
        /// <summary>
        ///    Remove the named edge from <c>src</c> to <c>dest</c>.
        ///    Abort transformation if the nodes do not exist.
        /// </summary>
        | RmNamedEdgeBetween of src : string * dest : string * name : string
        /// <summary>
        ///    Adds an edge combining the in edge <c>in</c> with the out
        ///    edge <c>out</c>.
        ///    Abort transformation if anything goes wrong.
        /// </summary>
        | MkCombinedEdge of inE : InEdge * outE : OutEdge
        /// <summary>
        ///    Adds an edge from <c>src</c> to <c>dest</c>.
        ///    Abort transformation if the nodes do not exist.
        /// </summary>
        | MkEdgeBetween of src : string * dest : string
                         * name : string * cmd : Command
        /// <summary>
        ///    Merges the node <c>src</c> into <c>dest</c>,
        ///    substituting the latter for the former in all edges.
        ///    How the unification handles edges is specified by
        ///    <see cref="UnifyType"/>.
        ///    Abort transformation if the nodes do not exist.
        /// </summary>
        | Unify of src : string * dest : string * mode : UnifyMode

    /// <summary>
    ///     A node-centric graph transformation context.
    /// </summary>
    type TransformContext =
        { /// <summary>
          ///     The current state of the graph.
          /// </summary>
          Graph : Graph
          /// <summary>
          ///     The node currently being inspected.
          ///     If None, the node has been removed and no longer needs
          ///     transformation.
          /// </summary>
          Node : string option
          /// <summary>
          ///     The log of transformations done, in reverse chronological
          ///     order.
          /// </summary>
          Transforms : Transform list
        }

    /// <summary>
    ///     Types of error that can happen in the term optimiser.
    /// </summary>
    type TermOptError =
        /// <summary>
        ///     An error occurred during traversal.
        /// </summary>
        | Traversal of TraversalError<TermOptError>

    /// <summary>
    ///     Types of error that can happen in the graph optimiser.
    /// </summary>
    type GraphOptError =
        /// <summary>
        ///     An error occurred during traversal.
        /// </summary>
        | Traversal of TraversalError<GraphOptError>

/// <summary>
///     Utilities common to the whole optimisation system.
/// </summary>
module Utils =
    /// <summary>
    ///     Parses an optimisation string list.
    /// </summary>
    /// <param name="opts">
    ///     A list of prefixes of optimisation names.
    ///     Optimisation name prefixes starting with 'no-' have this stripped
    ///     off, and the optimisation is negated.
    /// </param>
    /// <returns>
    ///     <para>
    ///         A list of tuples of (optimisation prefixes * enabled boolean)
    ///         If the optimisation is force enabled, the enabled boolean is true
    ///         otherwise it's false when force disabled.
    ///     </para>
    ///     <para>
    ///         As these strings are prefixes, 'graph' will switch on
    ///         all optimisations beginning with 'graph'.
    ///     </para>
    ///     <para>
    ///         The optimisation name 'all' is special.
    ///         It force-enables (or force-disables if 'no-all') all
    ///         optimisations.
    ///     </para>
    /// </returns>
    let parseOptimisationString (opts : string list) : (string * bool) list =
        opts
        |> List.map (fun (str : string) ->
            if str.StartsWith("no-") then
                (str.Remove(0, 3), false)
            else
                (str, true))

    /// <summary>
    ///     Decides whether an optimisation name matches an allowed
    ///     optimisation prefix.
    /// </summary>
    /// <param name="prefixes">
    ///     The set of allowed optimisation prefixes.
    /// </param>
    /// <param name="opt">
    ///     The optimisation name to check.
    /// </param>
    /// <returns>
    ///     True if <paramref name="opt" /> is allowed, according to
    ///     <paramref name="prefixes" />.
    /// </returns>
    let optAllowed (prefixes : Set<string>) (opt : string) : bool =
        // Check for the most obvious (and O(1)) case first.
        Set.contains opt prefixes ||
        Set.exists opt.StartsWith prefixes

    /// <summary>
    ///     Applies a pair of optimisation removes and adds to an optimisation
    ///     set.
    /// </summary>
    /// <param name="opts">
    ///     A list of triples of optimiser name, whether it's enabled by
    ///     default, and function.
    /// </param>
    /// <param name="removes">
    ///     The set of optimisation names to remove.  If this contains 'all',
    ///     no optimisations will be permitted.
    /// </param>
    /// <param name="adds">
    ///     The set of optimisation names to adds.  If this contains 'all',
    ///     all optimisations will be permitted.
    /// </param>
    /// <typeparam name="A">
    ///     The type of items being optimised.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of errors coming out of the optimiser.
    /// </typeparam>
    /// <returns>
    ///     A list of optimisers to run.
    /// </returns>
    let mkOptimiserList
      (allOpts : (string * bool * ('A -> Result<'A, 'Error>)) list)
      (opts : (string * bool) seq)
      : ('A -> Result<'A, 'Error>) list =
        let config = config()
        let optimisationSet = new HashSet<string>();
        // try add or remove from prefix
        let addFromPrefix prefix =
            for (optName : string, _, _) in allOpts do
                if optName.StartsWith(prefix) then
                    if config.verbose && not (optimisationSet.Contains(optName)) then
                        eprintfn "note: forced %s on" optName

                    ignore <| optimisationSet.Add(prefix)

        let removeFromPrefix prefix =
            for (optName, _, _) in allOpts do
                if optName.StartsWith(prefix) then
                    if config.verbose && optimisationSet.Contains(optName) then
                        eprintfn "note: forced %s off" optName

                    ignore <| optimisationSet.Remove(prefix)

        for (optName, enabledByDefault, _) in allOpts do
            if enabledByDefault then
                ignore <| optimisationSet.Add(optName)

        for (optName, forceEnabled) in opts do
            if optName = "all" then
                if forceEnabled then
                    if config.verbose then
                        eprintfn "note: forced all optimisations on"
                    for (optName, enabledByDefault, _) in allOpts do
                        ignore <| optimisationSet.Add(optName)
                else
                    if config.verbose then
                        eprintfn "note: forced all optimisations off"
                    optimisationSet.Clear()
            else

                if forceEnabled then
                    addFromPrefix optName
                else
                    removeFromPrefix optName


        List.filter (fun (name, _, _) -> optimisationSet.Contains(name)) allOpts
        |> List.map (fun (_, _, f) -> f)

    /// <summary>
    ///     Discovers which optimisers to activate, and applies them in
    ///     the specified order.
    ///
    ///     Each optimisation comes as a triple
    ///         (optimisation-name : string, enabled-as-default? : bool, optimisation: ('a -> 'a))
    ///
    ///     Enabling or disabling them based off the command-line arguments and whether they're enabled by default
    /// </summary>
    /// <param name="removes">
    ///     The set of optimisation names to remove.  If this contains 'all',
    ///     no optimisations will be permitted.
    /// </param>
    /// <param name="adds">
    ///     The set of optimisation names to add.  If this contains 'all',
    ///     all optimisations will be permitted.
    /// </param>
    /// <param name="opts">
    ///     A list of triples of optimiser name, whether it's enabled by
    ///     default, and function.
    /// </param>
    /// <typeparam name="A">
    ///     The type of the item to optimise.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of errors coming out of the optimiser.
    /// </typeparam>
    /// <returns>
    ///     A function that, when applied to something, optimises it with
    ///     the selected optimisers.
    /// </returns>
    let optimiseWith
      (args : (string * bool) list)
      (opts : (string * bool * ('A -> Result<'A, 'Error>)) list)
      : ('A -> Result<'A, 'Error>) =
        let fs = mkOptimiserList opts args

        (* This would be much more readable if it wasn't pointfree...
           ...but would also cause fs to be evaluated every single time
           the result of partially applying optimiseWith to removes, adds,
           verbose and opts is then applied to the input!  Oh, F#.  *)
        ok >> (flip (List.fold (flip bind)) fs)

/// <summary>
///     Graph optimisation.
/// </summary>
module Graph =
    open Starling.Core.Axiom
    open Starling.Core.Graph

    /// <summary>
    ///     Safely stitches the names of two edges together.
    /// </summary>
    /// <param name="_arg1">
    ///     The first edge, heading in.
    /// </param>
    /// <param name="_arg2">
    ///     The second edge, heading out.
    /// </param>
    /// <returns>
    ///     A name for any edge replacing both above edges.
    /// </returns>
    let glueNames ({ Name = a } : InEdge) ({ Name = b } : OutEdge) : string =
        String.concat "__" [ a ; b ]

    /// <summary>
    ///     Selects all of the connecting out-edges between two nodes.
    /// </summary>
    /// <param name="x">The first node to check.</param>
    /// <param name="y">The second node to check.</param>
    /// <param name="graph">The graph to check.</param>
    /// <returns>
    ///     The set of <see cref="OutEdge"/c>s connecting <paramref name="x"/>
    ///     to <paramref name="y"/> and <paramref name="y"/> to
    ///     <paramref name="x"/>.
    /// </returns>
    let connections (x : NodeID) (y : NodeID) (graph : Graph) : OutEdge seq =
        let xView, xOut, _, xnk = graph.Contents.[x]
        let yView, yOut, _, ynk = graph.Contents.[y]

        let xToY = xOut |> Set.toSeq |> Seq.filter (fun { Dest = d } -> d = y)
        let yToX = yOut |> Set.toSeq |> Seq.filter (fun { Dest = d } -> d = x)

        Seq.append xToY yToX


    /// <summary>
    ///     Runs a graph transformation.
    /// </summary>
    /// <param name="ctx">
    ///     The transformation context to transform.
    /// </param>
    /// <param name="xform">
    ///     The transform to perform.
    /// </param>
    /// <returns>
    ///     An Option.  If None, the transformation did not apply.
    ///     Otherwise, the Option contains the new transformation context.
    /// </returns>
    let runTransform (ctx : TransformContext) (xform : Transform)
      : TransformContext option =
        let f =
            match xform with
            | RmNode node -> rmNode node
            // All of these commands can be implemented the same way!
            | RmInEdge ({ Src = src ; Name = name }, dest)
                | RmOutEdge (src, { Dest = dest ; Name = name } )
                | RmNamedEdgeBetween (src, dest, name) ->
                rmEdgesBetween src dest ((=) name)
            | RmAllEdgesBetween (src, dest) -> rmEdgesBetween src dest always
            | MkCombinedEdge (inE, outE) ->
                mkEdgeBetween inE.Src
                              outE.Dest
                              (glueNames inE outE)
                              (inE.Command @ outE.Command)
            | MkEdgeBetween (src, dest, name, cmd) ->
                mkEdgeBetween src dest name cmd
            | Unify (src, dest, mode) ->
                match mode with
                | MakeConnectionsCycles -> unify src dest
                | RemoveConnections ->
                    // NB: rmEdgesBetween only removes in one direction!
                    rmEdgesBetween src dest always
                    >> Option.bind (rmEdgesBetween dest src always)
                    >> Option.bind (unify src dest)
                | OnlyIfNoConnections ->
                    fun graph ->
                        if Seq.isEmpty (connections src dest graph)
                        then unify src dest graph
                        else Some graph

        let node' =
            match xform with
            | RmNode n when Some n = ctx.Node -> None
            | _ -> ctx.Node

        ctx.Graph
        |> f
        |> Option.map (fun g -> { Graph = g
                                  Node = node'
                                  Transforms = xform :: ctx.Transforms } )

    /// <summary>
    ///     Runs a graph transformation list.
    ///
    ///     If any transformation step fails, the initial context is
    ///     returned, rewinding the transformations.
    /// </summary>
    /// <param name="xforms">
    ///     The set of transforms to perform.
    /// </param>
    /// <param name="initial">
    ///     A initial transformation context (to allow transformation results
    ///     to compose).
    /// </param>
    /// <returns>
    ///     The final transformation context.
    ///     If the list of transformations has not changed from
    ///     <paramref name="initial" />, the transformation list was rewound.
    /// </returns>
    let runTransforms
      (xforms : Transform seq)
      (initial : TransformContext)
      : TransformContext =
        match (foldFastTerm runTransform initial xforms) with
        | Some final -> final
        | None -> initial


    /// <summary>
    ///     Decides whether two nodes have different names but the same view,
    ///     and are connected, but only by no-op commands.
    /// </summary>
    /// <param name="graph">
    ///     The graph on which <paramref name="x" /> and
    ///     <paramref name="y" /> lie.
    /// </param>
    /// <param name="x">
    ///     The name of one of the nodes to consider.
    /// </param>
    /// <param name="y">
    ///     The name of the other node to consider.
    /// </param>
    /// <returns>
    ///     <c>true</c> if, and only if, <paramref name="x" />
    ///     and <paramref name="y" /> have different names, have the same
    ///     view, and are connected, but only by no-op commands.
    /// </returns>
    let nopConnected (graph : Graph) (x : NodeID) (y : NodeID) : bool =
        let xView, _, _, _ = graph.Contents.[x]
        let yView, _, _, _ = graph.Contents.[y]
        let cons = connections x y graph

        // Different names?
        (x <> y)
        // Same view?
        && (xView = yView)
        // Connected?
        && not (Seq.isEmpty cons)
        // All edges from x to y and y to x are nop?
        && Seq.forall (fun { OutEdge.Command = c } -> List.forall isNop c) cons

    /// <summary>
    ///     Plumbs a function over various properties of a graph and
    ///     node into the format expected by <c>onNodes</c>.
    /// </summary>
    /// <param name="ctx">
    ///     The transformation context.
    /// </param>
    /// <param name="f">
    ///     The function, which takes:
    ///     the name of the node;
    ///     the view of the node;
    ///     the out-edges of the node;
    ///     the in-edges of the node.
    ///
    ///     It should return a transformation sequence.
    /// </param>
    /// <returns>
    ///     If <paramref name="node" /> exists in the graph, the result of
    ///     calling <paramref name="f" /> and running the resulting
    ///     transformations.
    ///     Else, the original context.
    /// </returns>
    let expandNodeIn
      (ctx : TransformContext)
      (f : NodeID -> GraphViewExpr -> Set<OutEdge> -> Set<InEdge>
           -> NodeKind -> Transform seq)
      : TransformContext =
        let findNode n = Option.map (mkPair n) (ctx.Graph.Contents.TryFind n)

        match Option.bind findNode ctx.Node with
        | Some (nN, (nV, outs, ins, nk)) ->
            let xforms = f nN nV outs ins nk
            runTransforms xforms ctx
        | None -> ctx

    /// <summary>
    ///     Given a node, tries to unify every other node that is
    ///     equivalent and connected, but only by no-op commands, into it.
    /// </summary>
    /// <param name="ctx">
    ///     The transformation context.
    /// </param>
    /// <returns>
    ///     A triple containing the list of node names removed, a graph,
    ///     and the input node Option.
    ///     The graph is equivalent to <paramref name="g" />, but with some
    ///     nodes merged into the named node if they are
    ///     equivalent and connected only by no-op commands.
    /// </returns>
    let collapseNops (ctx : TransformContext) : TransformContext =
        let opt node nView outEdges inEdges nk =
            let outNodes = outEdges
                           |> Set.toSeq
                           |> Seq.map (fun { Dest = d } -> d)
            let inNodes = inEdges
                          |> Set.toSeq
                          |> Seq.map (fun { Src = s } -> s)

            Seq.append outNodes inNodes
            // Then, find out which ones are nop-connected.
            |> Seq.filter (nopConnected ctx.Graph node)
            (* If we found any nodes, then unify them.
               We must also remove the edges between the nodes. *)
            |> Seq.map (fun other -> Unify (other, node, RemoveConnections))
        expandNodeIn ctx opt

    /// <summary>
    ///     Decides whether a command is local.
    /// </summary>
    /// <param name="tVars">
    ///     A <c>VarMap</c> of thread-local variables.
    /// </param>
    /// <param name="cmd">The command to check.</param>
    /// <returns>
    ///     A function returning True only if (but not necessarily if)
    ///     the given command is local (uses only local variables).
    /// </returns>
    let isLocalCommand (tVars : VarMap) (cmd : Command) : bool =
        // TODO(CaptainHayashi): overlap with isLocalResults?
        let typedVarIsThreadLocal var =
             match tVars.TryFind (valueOf var) with
             | Some _ -> true
             | _ -> false

        let isLocalArg arg =
            // Forbid symbols in arguments.
            match (mapTraversal (removeSymFromExpr ignore) arg) with
                // TODO(CaptainHayashi): propagate if traversal error
                | Bad _ -> false
                | Ok (sp, _) ->
                    // Now check if all the variables in the argument are local.
                    let getVars = tliftOverExpr collectVars
                    match findVars getVars sp with
                    | Bad _ -> false
                    | Ok (pvars, _) ->
                        Seq.forall typedVarIsThreadLocal (Set.toSeq pvars)

        let isLocalPrim prim =
            match prim with
            | // TODO(CaptainHayashi): too conservative?
              SymC _ -> false
            | Intrinsic (IAssign { AssignType = t })
            | Intrinsic (BAssign { AssignType = t }) -> t = Local
            | Stored { Args = ps } -> Seq.forall isLocalArg ps

        List.forall isLocalPrim cmd

    /// Decides whether a given Command contains any `assume` command
    /// in any of the sequentially composed primitives inside it
    let hasAssume (c : Command) : bool =
        List.exists isAssume c


    /// <summary>
    ///     Partial active pattern matching <c>Sym</c>-less Boolean expressions.
    /// </summary>
    let (|NoSym|_|) (bexpr : BoolExpr<Sym<'Var>>) : BoolExpr<'Var> option =
        bexpr
        |> mkTypedSub normalBoolRec
        |> mapTraversal (removeSymFromBoolExpr ignore)
        |> okOption

    /// <summary>
    ///     Partial active pattern matching <c>Sym</c>-less expressions.
    /// </summary>
    let (|NoSymE|_|) (expr : Expr<Sym<'Var>>) : Expr<'Var> option =
        expr
        |> mapTraversal (removeSymFromExpr ignore)
        |> okOption


    /// <summary>
    ///     Active pattern matching on if-then-else guard multisets.
    ///
    ///     <para>
    ///         If-then-else guardsets contain two non-false guards, at least one
    ///         of which is equal to the negation of the other.
    ///         Neither guard can be symbolic.
    ///     </para>
    ///
    ///     <para>
    ///         The active pattern returns the guard and view of the first ITE
    ///         guard, then the guard and view of the second.  The views are
    ///         <c>GView</c>s, but with a <c>BTrue</c> guard.
    ///     </para>
    /// </summary>
    let (|ITEGuards|_|) (ms: IteratedGView<Sym<Var>>)
      : (BoolExpr<Var> * IteratedGView<Sym<Var>>
         * BoolExpr<Var> * IteratedGView<Sym<Var>>) option =
        match (Multiset.toFlatList ms) with
        | [ { Func = { Cond = NoSym xc; Item = xi }; Iterator = xit }
            { Func = { Cond = NoSym yc; Item = yi }; Iterator = yit } ]
              when (equivHolds id (negates xc yc)) ->
            Some (xc, Multiset.singleton { Func = { Cond = BTrue; Item = xi }; Iterator = xit },
                  yc, Multiset.singleton { Func = { Cond = BTrue; Item = yi }; Iterator = yit })
        // {| G -> P |} is trivially equivalent to {| G -> P * ¬G -> emp |}.
        | [ { Func = { Cond = NoSym xc; Item = xi }; Iterator = it } ] ->
            Some (xc, Multiset.singleton { Func = { Cond = BTrue; Item = xi }; Iterator = it },
                  mkNot xc, Multiset.empty)
        | _ -> None

    /// <summary>
    ///     Removes a node if it is an ITE-guarded view.
    ///
    ///     <para>
    ///         An ITE-guarded view is a view with one in-edge,
    ///         two guarded funcs which negate each other, and two
    ///         out-edges, each assuming one of the guards.
    ///     </para>
    /// </summary>
    /// <param name="ctx">
    ///     The transformation context.
    /// </param>
    /// <returns>
    ///     A triple containing the list of edge names removed, an
    ///     optimised graph, and an Option containing the node name if it was
    ///     not removed.
    /// </returns>
    let collapseITEs (ctx : TransformContext) : TransformContext =
        (* This checks whether, given a pairs (x, y) of assume A and target
           view V, they project onto a pair (i, j) of assume A and target
           node N in the given order. *)
        let iteProjectsInOrder xA xV yA yV iA iN jA jN =
            let projectA =
                equivHolds id (andEquiv (equiv xA iA) (equiv yA jA))
            let projectP =
                nodeHasView iN xV ctx.Graph && nodeHasView jN yV ctx.Graph
            projectA && projectP

        (* As above, but in either order:
           either (x, y) maps onto (i, j), or (x, y) maps onto (j, i). *)
        let iteProjects xA xV yA yV iA iN jA jN =
            // Is the first one x and the second y?
            iteProjectsInOrder xA xV yA yV iA iN jA jN
            // Or is the first one y and the second x?
            || iteProjectsInOrder xA xV yA yV jA jN iA iN

        let opt node nView outEdges inEdges nk =
            match nView with
            | InnerView(ITEGuards (xA, xV, yA, yV)) ->
                match (Set.toList outEdges, Set.toList inEdges) with
                (* Are there only two out edges, and only one in edge?
                    Are the out edges assumes, and are they non-symbolic? *)
                | ( [ { Dest = iN; Command = Assume (NoSym iA) } as out1
                      { Dest = jN; Command = Assume (NoSym jA) } as out2 ],
                    [ inE ] )
                    when iteProjects xA xV yA yV iA iN jA jN ->
                        seq { // Remove the existing edges first.
                              yield RmInEdge (inE, node)
                              yield RmOutEdge (node, out1)
                              yield RmOutEdge (node, out2)
                              // Then, remove the node.
                              yield RmNode node
                              // Then, add the new edges.
                              yield MkCombinedEdge (inE, out1)
                              yield MkCombinedEdge (inE, out2) }
                | _ -> Seq.empty
            | _ -> Seq.empty
        expandNodeIn ctx opt

    /// <summary>
    ///     Removes views where either all of the entry commands are local,
    ///     or all of the exit commands are local, and the view is advisory.
    /// </summary>
    /// <param name="locals">
    ///     The environment of local variables, used to determine whether
    ///     commands are local.
    /// </param>
    /// <param name="ctx">
    ///     The transformation context.
    /// </param>
    /// <returns>
    ///     A triple containing the list of edge names removed, an
    ///     optimised graph, and an Option containing the node name if it was
    ///     not removed.
    /// </returns>
    let dropLocalMidView (locals : VarMap) (ctx : TransformContext)
      : TransformContext =
        let opt nName nView outEdges inEdges nk =
            (* TODO @mjp41: Need to check nView is not something with a real definition *)

            if nk = Normal  // Check it is not an Entry or Exit node.
               (* Only continue if there is one edge for either the in or
                  out direction. *)
               && ((Set.count outEdges < 2) || (Set.count inEdges < 2))
               && ((Set.count outEdges > 0) && (Set.count inEdges > 0))
               // Only continue if the node can be safely removed.
               && isAdvisory nView
              (* Only continue if there are no cycles *)
               && (Set.forall (fun (e : OutEdge) -> e.Dest <> nName) outEdges)
               && (Set.forall (fun (e : InEdge) -> e.Src <> nName) inEdges)
               (* Commands must be local on either the in or the out.*)
               && ((Set.forall (fun (e : OutEdge) -> isLocalCommand locals e.Command) outEdges)
                  || (Set.forall (fun (e : InEdge) -> isLocalCommand locals e.Command) inEdges))
            then
                seq {
                    for inE in inEdges do
                        yield RmInEdge (inE, nName)

                        for outE in outEdges do
                            yield MkCombinedEdge (inE, outE)

                    for outE in outEdges do
                        yield RmOutEdge (nName, outE)

                    yield RmNode nName
                }
            else Seq.empty
        expandNodeIn ctx opt

    /// Drops edges with local results that are disjoint from
    /// the vars in the pre/post condition views
    /// i.e. given {| p |} c {| p |} drop iff Vars(p) n Vars(c) = {}
    let dropLocalEdges (locals : VarMap) (ctx : TransformContext)
      : TransformContext =
        let opt node nView outEdges inEdges nk =
            let disjoint (a : TypedVar list) (b : Set<TypedVar>) = List.forall (b.Contains >> not) a

            let processEdge (e : OutEdge) =
                if isLocalResults locals e.Command
                then
                    let pViewexpr = nView
                    let qViewexpr = (fun (viewexpr, _, _, _) -> viewexpr) <| ctx.Graph.Contents.[e.Dest]
                    // strip away mandatory/advisory and just look at the internal view
                    // (TODO: do something with the ViewExpr annotations?)
                    match (pViewexpr, qViewexpr) with
                    | InnerView pView, InnerView qView ->
                        let varResultSet = Set.map iteratedGFuncVars (Multiset.toSet pView)
                        let varsResults = lift Set.unionMany (collect varResultSet)
                        let cmdVarsResults = commandResultVars e.Command
                        // TODO: Better equality?
                        match varsResults, cmdVarsResults with
                        | Ok (vars, _), Ok (cmdVars, _) ->
                            // TODO: Better equality?
                            if pView = qView && disjoint (Set.toList cmdVars) vars
                            then
                                seq {
                                    yield RmOutEdge (node, e)
                                    yield Unify (node, e.Dest, OnlyIfNoConnections)
                                }
                            else Seq.empty
                        | _, _ -> Seq.empty
                else Seq.empty
            seq { for e in outEdges do yield! (processEdge e) }

        expandNodeIn ctx opt

    /// <summary>
    ///     Decides whether a system {p}c{q}d{r} can be collapsed to {p}d{r}.
    /// </summary>
    let canCollapseUnobservable
      (tvars : VarMap)
      (graph : Graph)
      (p : NodeID)
      (c : Command)
      (q : NodeID)
      (d : Command)
      (r : NodeID)
      : bool =
        // We can't collapse {p}c{p}d{r} or {p}c{r}d{r}.
        let noCycle = p <> q && q <> r

        // We can't collapse if {q} is mandatory.
        let qViewexpr, _, _, _ = graph.Contents.[q]
        let qAdvisory = match qViewexpr with | Advisory _ -> true | _ -> false

        let cHidden =
            match isObservable tvars c d with
            | Pass false -> true
            | _ -> false

        noCycle && qAdvisory && cHidden

    /// Collapses edges {p}c{q}d{r} to {p}d{r} iff c is unobservable
    /// i.e. c writes to local variables overwritten by d
    /// d does not read outputs of c,
    /// and there are no assumes adding information
    let collapseUnobservableEdges (tvars : VarMap) (ctx : TransformContext)
      : TransformContext =
        let opt node pViewexpr outEdges inEdges nodeKind =
            let disjoint (a : Set<'a>) (b : Set<'a>) =
                Set.empty = Set.filter b.Contains a
            let processCEdge cEdge =
                let dEdges = (fun (_, outs, _, _) -> outs) <| ctx.Graph.Contents.[cEdge.Dest]
                let processDEdge dEdge =
                    (pViewexpr, cEdge, dEdge)
                Set.map processDEdge dEdges

            let processTriple (pViewexpr, (cEdge : OutEdge), (dEdge : OutEdge)) =
                let c, d = cEdge.Command, dEdge.Command
                if canCollapseUnobservable tvars ctx.Graph node c cEdge.Dest d dEdge.Dest
                then
                    seq {
                        // Remove the {p}c{q} edge
                        yield RmOutEdge (node, cEdge)
                        // Remove the {q}d{r} edge
                        yield RmOutEdge (cEdge.Dest, dEdge)
                        // Remove q
                        yield RmNode cEdge.Dest
                        // Then, add the new edges {p}d{q}
                        yield MkCombinedEdge
                            ({ Name = node;       Src = dEdge.Dest;   Command = d },
                             { Name = dEdge.Dest; Dest = node;        Command = d })
                    }
                else Seq.empty

            let triples = Set.fold (+) Set.empty <| Set.map processCEdge outEdges
            seq { for triple in triples do yield! (processTriple triple) }
        expandNodeIn ctx opt


    /// <summary>
    ///     Performs a node-wise optimisation on every node in the graph.
    /// </summary>
    /// <param name="opt">
    ///     The optimisation, which must take a list of edges currently
    ///     removed, a graph, and a node to optimise.  It must return a tuple
    ///     of the new list of edges removed, and optimised graph.
    /// </param>
    /// <param name="graph">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     A graph equivalent to <paramref name="graph" />, but with the
    ///     node optimisation <paramref name="opt" /> performed as many times
    ///     as possible.
    /// </returns>
    let rec onNodes
      (opt : TransformContext -> Result<TransformContext, GraphOptError>)
      (graph : Graph)
      : Result<Graph, GraphOptError> =
        // TODO(CaptainHayashi): do a proper depth-first search instead.

        let graphResult =
            graph.Contents
            // Pull out nodeNames for removeIdStep.
            |> keys
            // Then, for each of those, try merging everything else into it.
            |> seqBind (fun node ctx -> opt { ctx with Node = Some node })
                       { Graph = graph ; Node = None ; Transforms = [] }

        (* Tail-recurse back if we did some optimisations.
           This is to see if we enabled more of them. *)
        bind
            (fun { Graph = newGraph; Transforms = xs } ->
                if (Seq.isEmpty xs)
                then ok newGraph
                else onNodes opt newGraph)
            graphResult

    /// <summary>
    ///     Optimises a graph.
    /// </summary>
    /// <param name="tvars">
    ///     The map of thread-local variables in action.
    /// </param>
    /// <param name="opts">
    ///     Set of optimisation toggles in action.
    /// </param>
    /// <param name="_arg1">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="_arg1" />.
    /// </returns>
    let optimiseGraph (tvars : VarMap) (opts : (string * bool) list)
      : Graph -> Result<Graph, GraphOptError> =
        // TODO(CaptainHayashi): make graph optiisations fail.
        onNodes
            (Utils.optimiseWith opts
                [ ("graph-collapse-nops", true, collapseNops >> ok)
                  ("graph-collapse-ites", true, collapseITEs >> ok)
                  ("graph-drop-local-edges", true, dropLocalEdges tvars >> ok)
                  ("graph-collapse-unobservable-edges", true, collapseUnobservableEdges tvars >> ok)
                  ("graph-drop-local-midview",true, dropLocalMidView tvars >> ok)
                ])

    /// <summary>
    ///     Optimises a model over graphs.
    /// </summary>
    /// <param name="opts">
    ///     Set of optimisation toggles in action.
    /// </param>
    /// <param name="mdl">
    ///     The model to optimise.
    /// </param>
    /// <param name="verbose">
    ///     Flag which, if enabled, causes non-default optimisation changes
    ///     to be reported to stderr.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="mdl" />.
    /// </returns>
    let optimise (opts : (string * bool) list) (mdl : Model<Graph, _>)
      : Result<Model<Graph, _>, GraphOptError> =
        tryMapAxioms (optimiseGraph mdl.ThreadVars opts) mdl


/// <summary>
///     Term optimisation.
/// </summary>
module Term =
    (*
     * After elimination
     *)

    /// Partial pattern that matches a Boolean expression in terms of exactly one /
    /// constant.
    let rec (|ConstantBoolFunction|_|) (x : BoolExpr<Sym<MarkedVar>>)
      : MarkedVar option =
        let tx = mkTypedSub normalBoolRec x
        tx
        |> findVars (tliftToBoolSrc (tliftToExprDest collectSymVars))
        |> okOption |> Option.map (Seq.map valueOf) |> Option.bind onlyOne

    /// Partial pattern that matches a Boolean expression in terms of exactly one /
    /// constant.
    let rec (|ConstantIntFunction|_|) (x : IntExpr<Sym<MarkedVar>>)
      : MarkedVar option =
        let tx = mkTypedSub normalIntRec x
        tx
        |> findVars (tliftToIntSrc (tliftToExprDest collectSymVars))
        |> okOption |> Option.map (Seq.map valueOf) |> Option.bind onlyOne

    /// Finds all instances of the pattern `x!after = f(x!before)` in an
    /// Boolean expression that is either an equality or conjunction, and
    /// where x is arithmetic.
    let rec findArithAfters
      : BoolExpr<Sym<MarkedVar>> -> (Var * IntExpr<Sym<MarkedVar>>) list =
        function
        | BIEq(IVar (Reg (After x)), (ConstantIntFunction (Before y) as fx))
            when x = y
            -> [(x, fx)]
        | BIEq(ConstantIntFunction (Before y) as fx, IVar (Reg (After x)))
            when x = y
            -> [(x, fx)]
        | BAnd xs -> concatMap findArithAfters xs
        | _ -> []

    /// Finds all instances of the pattern `x!after = f(x!before)` in a
    /// Boolean expression that is either an equality or conjunction, and
    /// where x is Boolean.
    let rec findBoolAfters
      : BoolExpr<Sym<MarkedVar>> -> (Var * BoolExpr<Sym<MarkedVar>>) list =
        function
        | BBEq(BVar (Reg (After x)), (ConstantBoolFunction (Before y) as fx))
            when x = y
            -> [(x, fx)]
        | BBEq(ConstantBoolFunction (Before y) as fx, BVar (Reg (After x)))
            when x = y
            -> [(x, fx)]
        | BAnd xs -> concatMap findBoolAfters xs
        | _ -> []

    /// Finds any Intermediate variables in constant boolean functions
    /// in the form x!inter i := f(x!_)
    /// and returns a list of ((intermediate:bigint * var: Var) * fx: BoolExpr)
    let rec findBoolInters
      : BoolExpr<Sym<MarkedVar>>
        -> ((bigint * Var) * BoolExpr<Sym<MarkedVar>>) list =
        function
        | BBEq (BVar (Reg (Intermediate(i, x))), (ConstantBoolFunction (Intermediate(k, y)) as fx))
        | BBEq (ConstantBoolFunction (Intermediate(k, y)) as fx, BVar (Reg (Intermediate(i, x))))
            when x = y
            ->
                if i > k then
                    [((i, x), fx)]
                else
                    []
        | BBEq (BVar (Reg (Intermediate(i, x))), (ConstantBoolFunction (Before y) as fx))
        | BBEq (BVar (Reg (Intermediate(i, x))), (ConstantBoolFunction (After y) as fx))
        | BBEq (ConstantBoolFunction (Before y) as fx, BVar (Reg (Intermediate(i, x))))
        | BBEq (ConstantBoolFunction (After y) as fx, BVar (Reg (Intermediate(i, x))))
            when x = y
            -> [((i, x), fx)]
        | BAnd xs -> concatMap findBoolInters xs
        | _ -> []

    /// Finds any Intermediate variables in constant integer functions
    /// in the form x!inter i := f(x!_)
    /// and returns a list of ((intermediate:bigint * var: Var) * fx: IntExpr)
    let rec findArithInters
      : BoolExpr<Sym<MarkedVar>>
        -> ((bigint * Var) * IntExpr<Sym<MarkedVar>>) list =
        function
        | BIEq (IVar (Reg (Intermediate(i, x))), (ConstantIntFunction (Intermediate(k, y)) as fx))
        | BIEq (ConstantIntFunction (Intermediate(k, y)) as fx, IVar (Reg (Intermediate(i, x))))
            when x = y
            ->
                if i > k then
                    [((i, x), fx)]
                else
                    []
        | BIEq (IVar (Reg (Intermediate(i, x))), (ConstantIntFunction (Before y) as fx))
        | BIEq (IVar (Reg (Intermediate(i, x))), (ConstantIntFunction (After y) as fx))
        | BIEq (ConstantIntFunction (Before y) as fx, IVar (Reg (Intermediate(i, x))))
        | BIEq (ConstantIntFunction (After y) as fx, IVar (Reg (Intermediate(i, x))))
            when x = y
            -> [((i, x), fx)]
        | BAnd xs -> concatMap findArithInters xs
        | _ -> []

    /// Lifts a set of after-variable substitutions to a traversal.
    let afterSubs
      (isubs : Map<Var, IntExpr<Sym<MarkedVar>>>)
      (bsubs : Map<Var, BoolExpr<Sym<MarkedVar>>>)
      : Traversal<CTyped<MarkedVar>, Expr<Sym<MarkedVar>>, TermOptError, unit> =
        (* TODO(CaptainHayashi): just use one Map<Var, Expr<_>>, and raise a
           traversal error if we get the wrong type out.
           TODO(CaptainHayashi): type safety? *)
        let switch =
            function
            | Int (ty, After a) ->
                Int (ty, Map.tryFind a isubs |> withDefault (siAfter a))
            | Bool (ty, After a) ->
                Bool (ty, Map.tryFind a bsubs |> withDefault (sbAfter a))
            | x -> mkVarExp (mapCTyped Reg x)
        ignoreContext (switch >> ok)

    /// Lifts a set of intermediate-variable substitutions to a traversal.
    let interSubs
      (isubs : Map<bigint * Var, IntExpr<Sym<MarkedVar>>>)
      (bsubs : Map<bigint * Var, BoolExpr<Sym<MarkedVar>>>)
      : Traversal<CTyped<MarkedVar>, Expr<Sym<MarkedVar>>, TermOptError, unit> =
        (* TODO(CaptainHayashi): just use one Map<Var, Expr<_>>, and raise a
           traversal error if we get the wrong type out.
           TODO(CaptainHayashi): type safety? *)
        let switch =
            function
            | Int (ty, Intermediate (i, a)) ->
                Int (ty, Map.tryFind (i, a) isubs |> withDefault (siInter i a))
            | Bool (ty, Intermediate (i, a)) ->
                Bool (ty, Map.tryFind (i, a) bsubs |> withDefault (sbInter i a))
            | x -> mkVarExp (mapCTyped Reg x)
        ignoreContext (switch >> ok)

    /// Eliminates bound before/after pairs in the term.
    /// If x!after = f(x!before) in the action, we replace x!after with
    /// f(x!before) in the precondition and postcondition.
    let eliminateAfters
      (term : CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc> )
      : Result<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>, TermOptError> =
        // TODO(CaptainHayashi): make this more general and typesystem agnostic.
        let sub = afterSubs (term.Cmd.Semantics |> findArithAfters |> Map.ofList)
                            (term.Cmd.Semantics |> findBoolAfters  |> Map.ofList)

        (* The substitution in term.Cmd will create a tautology
         * f(x!before) = f(x!before).
         * We assume we can eliminate it later.
         *)

        let trav =
            tliftOverCmdTerm
                (tliftToExprSrc (tliftToTypedSymVarSrc sub))
        let result = mapTraversal trav term
        mapMessages TermOptError.Traversal result

    let eliminateInters
      : CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>
        -> Result<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                  TermOptError> =
        fun term ->
        let sub = interSubs (term.Cmd.Semantics |> findArithInters |> Map.ofList)
                            (term.Cmd.Semantics |> findBoolInters  |> Map.ofList)

        let trav =
            tliftOverCmdTerm
                (tliftToExprSrc (tliftToTypedSymVarSrc sub))
        let result = mapTraversal trav term
        mapMessages TermOptError.Traversal result

    (*
     * Guard reduction
     *)

    /// Reduce a Boolean expression, given some known facts.
    let rec reduce (fs : Set<BoolExpr<Sym<MarkedVar>>>)
      : BoolExpr<Sym<MarkedVar>> -> BoolExpr<Sym<MarkedVar>> =
        function
        | x when Set.contains x fs -> BTrue
        | x when Set.contains (mkNot x) fs -> BFalse
        | BAnd xs -> mkAnd (List.map (reduce fs) xs)
        | BOr xs -> mkOr (List.map (reduce fs) xs)
        // TODO(CaptainHayashi: handle subtypes properly here?)
        | TBBEq (x, y) ->
            mkEq
                (typedBoolToExpr (mapTypedSub (reduce fs) x))
                (typedBoolToExpr (mapTypedSub (reduce fs) y))
        | BNot x -> mkNot (reduce fs x)
        | x -> x

    /// Reduce a GView, given some known facts.
    let reduceGView
      (fs : Set<BoolExpr<Sym<MarkedVar>>>)
      : GView<Sym<MarkedVar>> -> GView<Sym<MarkedVar>> =
      mapConds (reduce fs) >> pruneGuardedSet

    /// Reduce the guards in a Term.
    let guardReduce
      ({Cmd = c; WPre = w; Goal = g} : CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>)
      : Result<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
               TermOptError> =

        let fs = Set.ofList (unfoldAnds c.Semantics)
        ok {Cmd = c; WPre = reduceGView fs w; Goal = g}

    (*
     * Boolean simplification
     *)

    /// Performs expression simplification on a term.
    let simpTerm
      : CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>
        -> Result<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                  TermOptError> =
        let simpExpr : Expr<Sym<MarkedVar>> -> Expr<Sym<MarkedVar>> =
            function
            | Bool (ty, b) -> Bool (ty, simp b)
            | x -> x
        let sub = ignoreContext (simpExpr >> ok)
        let trav = tliftOverCmdTerm sub
        mapTraversal trav >> mapMessages TermOptError.Traversal

    (*
     * Frontend
     *)

    /// Optimises a model's terms.
    let optimise
      (opts : (string * bool) list)
      : Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>, _>
      -> Result<Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>, _>,
                TermOptError> =
        let optimiseTerm =
            Utils.optimiseWith opts
                [ ("term-remove-after", true, eliminateAfters)
                  ("term-remove-inters", true, eliminateInters)
                  ("term-reduce-guards", true, guardReduce)
                  ("term-simplify-bools", true, simpTerm) ]
        tryMapAxioms optimiseTerm


/// <summary>
///     Pretty printers for the optimiser types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty
    /// <summary>
    ///     Pretty-prints a term optimiser error.
    /// </summary>
    /// <param name="err">The <see cref="TermOptError"/> to print.</param>
    /// <param name="returns">
    ///     The <see cref="Doc"/> resulting from printing
    ///     <paramref name="err"/>.
    /// </param>
    let rec printTermOptError (err : TermOptError) : Doc =
        match err with
        | TermOptError.Traversal err -> printTraversalError printTermOptError err
        |> error

    /// <summary>
    ///     Pretty-prints a graph optimiser error.
    /// </summary>
    /// <param name="err">The <see cref="GraphOptError"/> to print.</param>
    /// <param name="returns">
    ///     The <see cref="Doc"/> resulting from printing
    ///     <paramref name="err"/>.
    /// </param>
    let rec printGraphOptError (err : GraphOptError) : Doc =
        match err with
        | GraphOptError.Traversal err -> printTraversalError printGraphOptError err
        |> error
