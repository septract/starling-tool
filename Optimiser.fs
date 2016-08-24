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
open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Command.Queries
open Starling.Core.Sub
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Sub


/// <summary>
///     Types for the graph transformer.
/// </summary>
[<AutoOpen>]
module Types =
    open Starling.Core.Graph

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
        ///    All edges between the two become cycles on <c>dest</c>.
        ///    Abort transformation if the nodes do not exist.
        /// </summary>
        | Unify of src : string * dest : string

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
    /// <typeparam name="Fun">
    ///     The optimisation function type.
    /// </typeparam>
    /// <returns>
    ///     A list of optimisers to run.
    /// </returns>
    let mkOptimiserList
      (allOpts : (string * bool * 'Fun) list)
      (opts : (string * bool) seq)
      : 'Fun list =
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
    /// <typeparam name="a">
    ///     The type of the item to optimise.
    /// </typeparam>
    /// <returns>
    ///     A function that, when applied to something, optimises it with
    ///     the selected optimisers.
    /// </returns>
    let optimiseWith
      : (string * bool) list -> (string * bool * ('a -> 'a)) list -> ('a -> 'a) =
        fun args opts ->
        let fs = mkOptimiserList opts args

        (* This would be much more readable if it wasn't pointfree...
           ...but would also cause fs to be evaluated every single time
           the result of partially applying optimiseWith to removes, adds,
           verbose and opts is then applied to the input!  Oh, F#.  *)
        (flip (List.fold (|>)) fs)

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
            | Unify (src, dest) -> unify src dest

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
        let xView, xOut, xIn, xnk = graph.Contents.[x]
        let yView, _, _, ynk = graph.Contents.[y]

        let xToY =
            xOut |> Set.toSeq |> Seq.filter (fun { Dest = d } -> d = y)

        let yToX =
            xIn |> Set.toSeq |> Seq.filter (fun { Src = s } -> s = y)

        // Different names?
        (x <> y)
        // Same view?
        && (xView = yView)
        // Connected?
        && not (Seq.isEmpty xToY && Seq.isEmpty yToX)
        // All edges from x to y are nop?
        && Seq.forall (fun { OutEdge.Command = c } -> isNop c) xToY
        // All edges from y to x are nop?
        && Seq.forall (fun { InEdge.Command = c } -> isNop c) yToX

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
    ///     It should return a transformation context.
    /// </param>
    /// <returns>
    ///     If <paramref name="node" /> exists in the graph, the result of
    ///     calling <paramref name="f" />.  Else, the original context.
    /// </returns>
    let expandNodeIn
      (ctx : TransformContext)
      (f : NodeID -> GraphViewExpr -> Set<OutEdge> -> Set<InEdge>
           -> NodeKind -> TransformContext)
      : TransformContext =
        match (Option.bind (fun n -> Map.tryFind n ctx.Graph.Contents
                                     |> Option.map (fun r -> (n, r)))
                           ctx.Node) with
        | Some (nN, (nV, outs, ins, nk)) -> f nN nV outs ins nk
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
        expandNodeIn ctx <|
            fun node nView outEdges inEdges nk ->
                let outNodes = outEdges
                               |> Set.toSeq
                               |> Seq.map (fun { Dest = d } -> d)
                let inNodes = inEdges
                              |> Set.toSeq
                              |> Seq.map (fun { Src = s } -> s)

                let xforms =
                    Seq.append outNodes inNodes
                    // Then, find out which ones are nop-connected.
                    |> Seq.filter (nopConnected ctx.Graph node)
                    (* If we found any nodes, then unify them.
                               We must also remove the edges between the nodes. *)
                    |> Seq.map
                            (fun other ->
                                seq {
                                    yield RmAllEdgesBetween (node, other)
                                    yield RmAllEdgesBetween (other, node)
                                    yield Unify (other, node)
                                } )
                    |> Seq.concat

                runTransforms xforms ctx

    /// <summary>
    ///     Decides whether a command is local.
    /// </summary>
    /// <param name="tVars">
    ///     A <c>VarMap</c> of thread-local variables.
    /// </param>
    /// <returns>
    ///     A function returning True only if (but not necessarily if)
    ///     the given command is local (uses only local variables).
    /// </returns>
    let isLocalCommand (tVars : VarMap) : Command -> bool =
        // A command is local if, for all of its funcs...
        List.forall
            (fun { Args = ps } ->
                 // ...for all of the parameters in said funcs...
                 Seq.forall
                     (fun p ->
                          // ...there are no symbols, and...
                          match (Mapper.tryMapCtx (tsfRemoveSym (fun _ -> ())) NoCtx p) with
                          | _, Bad _ -> false
                          | _, _ ->
                              // ...for all of the variables in said parameters...
                              p
                              |> mapOverSMVars Mapper.mapCtx findSMVars
                              |> Set.toSeq
                              |> Seq.forall
                                     (// ...the variable is thread-local.
                                      valueOf
                                      >> function
                                         | (After x)
                                         | (Before x)
                                         | (Intermediate (_, x))
                                         | (Goal (_, x)) ->
                                           x
                                           |> tVars.TryFind
                                           |> function
                                              | Some _ -> true
                                              | _ -> false))
                     ps)

    /// Decides whether a given Command contains any `assume` command
    /// in any of the sequentially composed primitives inside it
    let hasAssume : Command -> bool =
        fun c ->
            c |>
            List.forall (
                function
                | { Name = "Assume" } -> true;
                | _ -> false)

    /// Determines if some given Command is local with respect to the given
    /// map of thread-local variables
    let isLocalResults : VarMap -> Command -> bool =
        fun tvars ->
        let localResults prim =
            List.forall (fun v ->
                match (tvars.TryFind <| valueOf v) with
                | Some x -> typeOf v = x
                | None   -> false
                ) prim.Results
        List.forall localResults

    /// <summary>
    ///     Partial active pattern matching <c>Sym</c>-less expressions.
    /// </summary>
    let (|VNoSym|_|) : BoolExpr<Sym<Var>> -> BoolExpr<Var> option =
        Mapper.mapBoolCtx (tsfRemoveSym (fun _ -> ())) NoCtx >> snd >> okOption

    /// <summary>
    ///     Partial active pattern matching <c>Sym</c>-less expressions.
    /// </summary>
    let (|MNoSym|_|) : BoolExpr<Sym<MarkedVar>> -> BoolExpr<MarkedVar> option =
        Mapper.mapBoolCtx (tsfRemoveSym (fun _ -> ())) NoCtx >> snd >> okOption


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
    let (|ITEGuards|_|) (ms: GView<Sym<Var>>)
      : (BoolExpr<Var> * GView<Sym<Var>>
         * BoolExpr<Var> * GView<Sym<Var>>) option =
        match (Multiset.toFlatList ms) with
        | [ { Cond = VNoSym xc; Item = xi }
            { Cond = VNoSym yc; Item = yi } ]
              when (equivHolds id (negates xc yc)) ->
            Some (xc, Multiset.singleton { Cond = BTrue; Item = xi },
                  yc, Multiset.singleton { Cond = BTrue; Item = yi })
        // {| G -> P |} is trivially equivalent to {| G -> P * ¬G -> emp |}.
        | [ { Cond = (VNoSym xc); Item = xi } ] ->
            Some (xc, Multiset.singleton { Cond = BTrue; Item = xi },
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
        expandNodeIn ctx <|
            fun node nView outEdges inEdges nk ->
                match nView with
                | InnerView(ITEGuards (xc, xv, yc, yv)) ->
                    (* Translate xc and yc to pre-state, to match the
                       commands. *)
                    let _, xcPre = Mapper.mapBoolCtx vBefore NoCtx xc
                    let _, ycPre = Mapper.mapBoolCtx vBefore NoCtx yc

                    match (Set.toList outEdges, Set.toList inEdges) with
                    (* Are there only two out edges, and only one in edge?
                       Are the out edges assumes, and are they non-symbolic? *)
                    | ( [ { Dest = out1D
                            Command = Assume (MNoSym out1P) } as out1
                          { Dest = out2D
                            Command = Assume (MNoSym out2P) } as out2
                        ],
                        [ inE ] )
                        when (// Is the first one x and the second y?
                              (equivHolds
                                   unmarkVar
                                   (andEquiv (equiv out1P xcPre)
                                             (equiv out2P ycPre))
                               && nodeHasView out1D xv ctx.Graph
                               && nodeHasView out2D yv ctx.Graph)
                              // Or is the first one y and the second x?
                              || (equivHolds
                                      unmarkVar
                                      (andEquiv (equiv out2P xcPre)
                                                (equiv out1P ycPre))
                                  && nodeHasView out2D xv ctx.Graph
                                  && nodeHasView out1D yv ctx.Graph)) ->
                        let xforms =
                            seq { // Remove the existing edges first.
                                  yield RmInEdge (inE, node)
                                  yield RmOutEdge (node, out1)
                                  yield RmOutEdge (node, out2)
                                  // Then, remove the node.
                                  yield RmNode node
                                  // Then, add the new edges.
                                  yield MkCombinedEdge (inE, out1)
                                  yield MkCombinedEdge (inE, out2) }
                        runTransforms xforms ctx
                    | _ -> ctx
                | _ -> ctx

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
        expandNodeIn ctx <|
            fun nName nView outEdges inEdges nk ->
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
                    let xforms = seq {
                        for inE in inEdges do
                            yield RmInEdge (inE, nName)

                            for outE in outEdges do
                                yield MkCombinedEdge (inE, outE)

                        for outE in outEdges do
                            yield RmOutEdge (nName, outE)

                        yield RmNode nName
                    }

                    runTransforms xforms ctx
                else
                    ctx

    /// Drops edges with local results that are disjoint from
    /// the vars in the pre/post condition views
    /// i.e. given {| p |} c {| p |} drop iff Vars(p) n Vars(c) = {}
    let dropLocalEdges (locals : VarMap) (ctx : TransformContext)
      : TransformContext =
        expandNodeIn ctx <|
            fun node nView outEdges inEdges nk ->
                let disjoint (a : TypedVar list) (b : Set<TypedVar>) = List.forall (fun v -> not <| b.Contains v) a
                let processEdge ctx (e : OutEdge) =
                    if isLocalResults locals e.Command
                        then
                            let pViewexpr = nView
                            let qViewexpr = (fun (viewexpr, _, _, _) -> viewexpr) <| ctx.Graph.Contents.[e.Dest]
                            // strip away mandatory/advisory and just look at the internal view
                            // (TODO: do something with the ViewExpr annotations?)
                            match (pViewexpr, qViewexpr) with
                            | InnerView pView, InnerView qView ->
                                let vars = SVGViewVars pView
                                let cmdVars = commandResults e.Command
                                // TODO: Better equality?
                                if pView = qView && disjoint cmdVars vars
                                    then
                                        (flip runTransforms) ctx
                                        <| seq {
                                            yield RmOutEdge (node, e)
                                        }
                                    else ctx
                        else ctx
                Set.fold processEdge ctx outEdges

    /// Collapses edges {p}c{q}d{r} to {p}d{r} iff c is unobservable
    /// i.e. c writes to local variables overwritten by d
    /// d does not read outputs of c,
    /// and there are no assumes adding information
    let collapseUnobservableEdges (locals : VarMap) (ctx : TransformContext)
      : TransformContext =
        expandNodeIn ctx <|
            fun node nViewexpr outEdges inEdges nodeKind ->
                let pViewexpr = nViewexpr
                let disjoint (a : Set<'a>) (b : Set<'a>) =
                    Set.empty = Set.filter b.Contains a
                let processCEdge cEdge =
                    let dEdges = (fun (_, outs, _, _) -> outs) <| ctx.Graph.Contents.[cEdge.Dest]
                    let processDEdge dEdge =
                        (pViewexpr, cEdge, dEdge)
                    Set.map processDEdge dEdges

                let processTriple ctx (pViewexpr, (cEdge : OutEdge), (dEdge : OutEdge)) =
                    let c, d = cEdge.Command, dEdge.Command

                    let qViewexpr = (fun (viewexpr, _, _, _) -> viewexpr) <| ctx.Graph.Contents.[cEdge.Dest]
                    let rViewexpr = (fun (viewexpr, _, _, _) -> viewexpr) <| ctx.Graph.Contents.[dEdge.Dest]

                    match (pViewexpr, qViewexpr, rViewexpr) with
                    | InnerView pView, InnerView qView, InnerView rView ->
                        let cResults = Set.ofList <| commandResults c
                        let dResults = Set.ofList <| commandResults d
                        let dArgs    = commandArgs d
                        if Set.isSubset cResults dResults
                            && disjoint cResults dArgs
                            && isLocalResults locals c
                            && not (hasAssume c)  // TODO: is this too broad?
                            && not (hasAssume d)  // TODO: is this necessary?
                            then
                                (flip runTransforms) ctx
                                <| seq {
                                      // Remove the {p}c{q} edge
                                      yield RmOutEdge (node, cEdge)
                                      // Remove the {q}d{r} edge
                                      yield RmOutEdge (cEdge.Dest, dEdge)
                                      // Remove q
                                      yield RmNode cEdge.Dest
                                      // Then, add the new edges {p}d{q}
                                      yield MkCombinedEdge
                                          ({ Name = node;       Src = dEdge.Dest;   Command = d },
                                          { Name = dEdge.Dest;  Dest = node;        Command = d })
                                }
                            else ctx

                let triples = Set.fold (+) Set.empty <| Set.map processCEdge outEdges
                Set.fold processTriple ctx triples


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
      (opt : TransformContext -> TransformContext)
      (graph : Graph)
      : Graph =
        // TODO(CaptainHayashi): do a proper depth-first search instead.

        let { Graph = newGraph ; Transforms = xs } =
            graph.Contents
            // Pull out nodeNames for removeIdStep.
            |> keys
            // Then, for each of those, try merging everything else into it.
            |> Seq.fold (fun ctx node -> opt { ctx with Node = Some node })
                        { Graph = graph ; Node = None ; Transforms = [] }

        (* Tail-recurse back if we did some optimisations.
           This is to see if we enabled more of them. *)
        if (Seq.isEmpty xs)
        then newGraph
        else onNodes opt newGraph

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
      : Graph -> Graph =
        onNodes (Utils.optimiseWith opts
                     [ ("graph-collapse-nops", true, collapseNops)
                       ("graph-collapse-ites", true, collapseITEs)
                       ("graph-drop-local-edges", true, dropLocalEdges tvars)
                       ("graph-collapse-unobservable-edges", true, collapseUnobservableEdges tvars)
                       ("graph-drop-local-midview",true, dropLocalMidView tvars)
                     ] )

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
      : Model<Graph, _> =
        mapAxioms (optimiseGraph mdl.Locals opts) mdl


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
        x |> mapOverSMVars Mapper.mapBoolCtx findSMVars |> Seq.map valueOf |> onlyOne

    /// Partial pattern that matches a Boolean expression in terms of exactly one /
    /// constant.
    let rec (|ConstantIntFunction|_|) (x : IntExpr<Sym<MarkedVar>>)
      : MarkedVar option =
        x |> mapOverSMVars Mapper.mapIntCtx findSMVars |> Seq.map valueOf |> onlyOne

    /// Finds all instances of the pattern `x!after = f(x!before)` in an
    /// Boolean expression that is either an equality or conjunction, and
    /// where x is arithmetic.
    let rec findArithAfters
      : BoolExpr<Sym<MarkedVar>> -> (Var * IntExpr<Sym<MarkedVar>>) list =
        function
        | BAEq(AVar (Reg (After x)), (ConstantIntFunction (Before y) as fx))
            when x = y
            -> [(x, fx)]
        | BAEq(ConstantIntFunction (Before y) as fx, AVar (Reg (After x)))
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
        | BAEq (AVar (Reg (Intermediate(i, x))), (ConstantIntFunction (Intermediate(k, y)) as fx))
        | BAEq (ConstantIntFunction (Intermediate(k, y)) as fx, AVar (Reg (Intermediate(i, x))))
            when x = y
            ->
                if i > k then
                    [((i, x), fx)]
                else
                    []
        | BAEq (AVar (Reg (Intermediate(i, x))), (ConstantIntFunction (Before y) as fx))
        | BAEq (AVar (Reg (Intermediate(i, x))), (ConstantIntFunction (After y) as fx))
        | BAEq (ConstantIntFunction (Before y) as fx, AVar (Reg (Intermediate(i, x))))
        | BAEq (ConstantIntFunction (After y) as fx, AVar (Reg (Intermediate(i, x))))
            when x = y
            -> [((i, x), fx)]
        | BAnd xs -> concatMap findArithInters xs
        | _ -> []

    /// Lifts a pair of before/after maps to a SubFun.
    let afterSubs
      (isubs : Map<Var, IntExpr<Sym<MarkedVar>>>)
      (bsubs : Map<Var, BoolExpr<Sym<MarkedVar>>>)
      : SubFun<Sym<MarkedVar>, Sym<MarkedVar>> =
        onVars
            (liftVToSym
                (Mapper.make
                    (function
                     | After a -> (Map.tryFind a isubs |> withDefault (siAfter a))
                     | x -> AVar (Reg x))
                    (function
                     | After a -> (Map.tryFind a bsubs |> withDefault (sbAfter a))
                     | x -> BVar (Reg x))))

    /// Creates a SubFun from intermediate substitutions
    let interSubs
      (isubs : Map<bigint * Var, IntExpr<Sym<MarkedVar>>>)
      (bsubs : Map<bigint * Var, BoolExpr<Sym<MarkedVar>>>)
      : SubFun<Sym<MarkedVar>, Sym<MarkedVar>> =
        onVars
            (liftVToSym
                (Mapper.make
                    (function
                     | Intermediate(i, a) -> (Map.tryFind (i, a) isubs |> withDefault (siInter i a))
                     | x -> AVar (Reg x))
                    (function
                     | Intermediate(i, a) -> (Map.tryFind (i, a) bsubs |> withDefault (sbInter i a))
                     | x -> BVar (Reg x))))

    /// Eliminates bound before/after pairs in the term.
    /// If x!after = f(x!before) in the action, we replace x!after with
    /// f(x!before) in the precondition and postcondition.
    let eliminateAfters
      (term : STerm<GView<Sym<MarkedVar>>, SMVFunc> )
      : STerm<GView<Sym<MarkedVar>>, SMVFunc> =
        let sub = afterSubs (term.Cmd |> findArithAfters |> Map.ofList)
                            (term.Cmd |> findBoolAfters  |> Map.ofList)

        (* The substitution in term.Cmd will create a tautology
         * f(x!before) = f(x!before).
         * We assume we can eliminate it later.
         *)
        subExprInDTerm sub NoCtx term |> snd

    let eliminateInters
      : STerm<GView<Sym<MarkedVar>>, SMVFunc>
        -> STerm<GView<Sym<MarkedVar>>, SMVFunc> =
        fun term ->
        let sub = interSubs (term.Cmd |> findArithInters |> Map.ofList)
                            (term.Cmd |> findBoolInters  |> Map.ofList)

        subExprInDTerm sub NoCtx term |> snd

    (*
     * Guard reduction
     *)

    /// Return all known facts inside a conjunctive Boolean expression.
    let rec facts
      : BoolExpr<Sym<MarkedVar>> -> BoolExpr<Sym<MarkedVar>> list =
        function
        | BAnd xs -> concatMap facts xs
        | x -> [x]

    /// Reduce a Boolean expression, given some known facts.
    let rec reduce (fs : Set<BoolExpr<Sym<MarkedVar>>>)
      : BoolExpr<Sym<MarkedVar>> -> BoolExpr<Sym<MarkedVar>> =
        function
        | x when Set.contains x fs -> BTrue
        | x when Set.contains (mkNot x) fs -> BFalse
        | BAnd xs -> mkAnd (List.map (reduce fs) xs)
        | BOr xs -> mkOr (List.map (reduce fs) xs)
        | BBEq (x, y) -> mkEq (reduce fs x |> Expr.Bool) (reduce fs y |> Expr.Bool)
        | BNot x -> mkNot (reduce fs x)
        | x -> x

    /// Reduce a GView, given some known facts.
    let reduceGView
      (fs : Set<BoolExpr<Sym<MarkedVar>>>)
      : GView<Sym<MarkedVar>> -> GView<Sym<MarkedVar>> =
      mapConds (reduce fs) >> pruneGuardedSet

    /// Reduce the guards in a Term.
    let guardReduce
      ({Cmd = c; WPre = w; Goal = g} : STerm<GView<Sym<MarkedVar>>, SMVFunc>)
      : STerm<GView<Sym<MarkedVar>>, SMVFunc> =

        let fs = c |> facts |> Set.ofList
        {Cmd = c; WPre = reduceGView fs w; Goal = g}

    (*
     * Boolean simplification
     *)

    /// Performs expression simplification on a term.
    let simpTerm
      : STerm<GView<Sym<MarkedVar>>, SMVFunc>
        -> STerm<GView<Sym<MarkedVar>>, SMVFunc> =
        subExprInDTerm (Mapper.make id simp) NoCtx >> snd

    (*
     * Frontend
     *)

    /// Term optimisers switched on by default.
    let defaultTermOpts : Set<string> =
        Set.ofList [ "term-remove-after"
                     "term-reduce-guards"
                     "term-simplify-bools" ]

    /// Optimises a model's terms.
    let optimise
      (opts : (string * bool) list)
      : Model<STerm<GView<Sym<MarkedVar>>, SMVFunc>, _>
      -> Model<STerm<GView<Sym<MarkedVar>>, SMVFunc>, _> =
        let optimiseTerm =
            Utils.optimiseWith opts
                [ ("term-remove-after", true, eliminateAfters)
                  ("term-remove-inters", true, eliminateInters)
                  ("term-reduce-guards", true, guardReduce)
                  ("term-simplify-bools", true, simpTerm) ]
        mapAxioms optimiseTerm
