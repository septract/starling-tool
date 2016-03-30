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

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Command.Queries
open Starling.Core.Sub
open Starling.Core.GuardedView


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
    ///         A tuple of two sets of optimisation prefixes.
    ///         The first is the set of optimisations force-disabled (names
    ///         beginning with no-).
    ///         The second is the set of optimisations force-enabled.
    ///         Each optimisation name is downcased.
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
    let parseOptString (opts : string list) =
        opts
        |> List.partition (fun str -> str.StartsWith("no-"))
        |> pairMap (Seq.map (fun s -> s.Remove(0, 3)) >> Set.ofSeq)
                   (Set.ofSeq)

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
    let optAllowed prefixes (opt : string) =
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
    /// <param name="verbose">
    ///     If true, add warnings when a default optimisation is overridden.
    /// </param>
    /// <returns>
    ///     A sequence of optimisers to run.
    /// </returns>
    let mkOptimiserSet opts removes adds verbose =
        if Set.contains "all" removes
        then
             if verbose
             then eprintfn "note: all optimisations disabled"

             []
        else if Set.contains "all" adds
        then
            if verbose
            then eprintfn "note: all optimisations enabled"

            List.map (fun (_, _, ofun) -> ofun) opts
        else
            opts
            |> Seq.choose
                   (fun (name, on, f) ->
                        let on' = (on || optAllowed adds name)
                                  && (not (optAllowed removes name))

                        if (verbose && (on' <> on))
                        then eprintfn "note: optimisation %s forced %s"
                                      name
                                      (if on' then "on" else "off")

                        if on' then Some f else None)
            (* We use List instead of Seq to make sure the above evaluates
               only once. *)
            |> List.ofSeq

    /// <summary>
    ///     Discovers which optimisers to activate, and applies them in
    ///     the specified order.
    /// </summary>
    /// <param name="removes">
    ///     The set of optimisation names to remove.  If this contains 'all',
    ///     no optimisations will be permitted.
    /// </param>
    /// <param name="adds">
    ///     The set of optimisation names to add.  If this contains 'all',
    ///     all optimisations will be permitted.
    /// </param>
    /// <param name="verbose">
    ///     If true, add warnings when a default optimisation is overridden.
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
    let optimiseWith removes adds verbose opts =
        let fs = mkOptimiserSet opts removes adds verbose

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
    let glueNames { InEdge.Name = a } { OutEdge.Name = b } =
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
    let runTransform (ctx : TransformContext) xform =
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
    let runTransforms xforms initial =
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
    let nopConnected graph x y =
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
    let expandNodeIn ctx f =
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
    let collapseNops ctx =
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
    let isLocalCommand tVars : Command -> bool =
        // A command is local if, for all of its funcs...
        List.forall
            (fun { Params = ps } ->
                 // ...for all of the parameters in said funcs...
                 Seq.forall
                     (// ...for all of the variables in said parameters...
                      varsIn
                      >> Set.toSeq
                      >> Seq.forall
                             (// ...the variable is thread-local.
                              fun c ->
                                  match (Map.tryFind (stripMark c) tVars) with
                                  | Some _ -> true
                                  | _ -> false))
                     ps)

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
    let collapseITEs ctx =
        expandNodeIn ctx <|
            fun node nView outEdges inEdges nk ->
                match nView with
                | ITEGuards (xc, xv, yc, yv) ->
                    (* Translate xc and yc to pre-state, to match the
                       commands. *)
                    let xcPre = (liftMarker Before always).BSub xc
                    let ycPre = (liftMarker Before always).BSub yc

                    match (Set.toList outEdges, Set.toList inEdges) with
                    (* Are there only two out edges, and only one in edge?
                       Are the out edges assumes? *)
                    | ( [ { Dest = out1D ; Command = Assume out1P } as out1
                          { Dest = out2D ; Command = Assume out2P } as out2
                        ],
                        [ inE ] )
                        when (// Is the first one x and the second y?
                              (equivHolds
                                   (andEquiv (equiv out1P xcPre)
                                             (equiv out2P ycPre))
                               && nodeHasView out1D xv ctx.Graph
                               && nodeHasView out2D yv ctx.Graph)
                              // Or is the first one y and the second x?
                              || (equivHolds
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
    ///     Removes views in the where either all of the entry commands are local, or
    ///     all of the exit commands are local.
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
    /// <remarks>
    ///     This removes a view that may be needed for the proof, so it is
    ///     turned off by default.
    /// </remarks>
    let dropLocalMidView locals ctx =
        expandNodeIn ctx <|
            fun nName nView outEdges inEdges nk ->
                (* TODO @mjp41: Need to check nName is not an entry or exit node from the CFG *)
                (* TODO @mjp41: Need to check nView is not something with a real definition *)

                if nk = Normal  // Check it is not an Entry or Exit node.
                   (* Only continue if there is one edge for either the in or
                      out direction. *)
                   && ((Set.count outEdges < 2) || (Set.count inEdges < 2))
                   && ((Set.count outEdges > 0) && (Set.count inEdges > 0))
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
    let rec onNodes opt graph =
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
    /// <param name="model">
    ///     The model whence the graph came.
    /// </param>
    /// <param name="optR">
    ///     Set of optimisations to suppress.
    /// </param>
    /// <param name="optA">
    ///     Set of optimisations to force.
    /// </param>
    /// <param name="verbose">
    ///     Flag which, if enabled, causes non-default optimisation changes
    ///     to be reported to stderr.
    /// </param>
    /// <param name="_arg1">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="_arg1" />.
    /// </returns>
    let optimiseGraph model optR optA verbose =
        // TODO(CaptainHayashi): Use the model for something.
        onNodes (Utils.optimiseWith optR optA verbose
                     [ ("graph-collapse-nops", true, collapseNops)
                       ("graph-collapse-ites", true, collapseITEs)
                       ("x-graph-drop-local-midview",
                        false,
                        dropLocalMidView model.Locals) ] )

    /// <summary>
    ///     Optimises a model over graphs.
    /// </summary>
    /// <param name="mdl">
    ///     The model to optimise.
    /// </param>
    /// <param name="optR">
    ///     Set of optimisations to suppress.
    /// </param>
    /// <param name="optA">
    ///     Set of optimisations to force.
    /// </param>
    /// <param name="verbose">
    ///     Flag which, if enabled, causes non-default optimisation changes
    ///     to be reported to stderr.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="mdl" />.
    /// </returns>
    let optimise optR optA verbose mdl =
        mapAxioms (optimiseGraph mdl optR optA verbose) mdl


/// <summary>
///     Term optimisation.
/// </summary>
module Term =
    (*
     * After elimination
     *)

    /// Finds all instances of the pattern `x!after = f(x!before)` in a
    /// Boolean expression that is either an equality or conjunction, and
    /// where x is arithmetic.
    let rec findArithAfters =
        function
        | BAEq(AConst(After x), (ConstantArithFunction (Before y) as fx))
            when x = y
            -> [(x, fx)]
        | BAEq(ConstantArithFunction (Before y) as fx, AConst(After x))
            when x = y
            -> [(x, fx)]
        | BAnd xs -> concatMap findArithAfters xs
        | _ -> []

    /// Finds all instances of the pattern `x!after = f(x!before)` in a
    /// Boolean expression that is either an equality or conjunction, and
    /// where x is Boolean.
    let rec findBoolAfters =
        function
        | BBEq(BConst(After x), (ConstantBoolFunction (Before y) as fx))
            when x = y
            -> [(x, fx)]
        | BBEq(ConstantBoolFunction (Before y) as fx, BConst(After x))
            when x = y
            -> [(x, fx)]
        | BAnd xs -> concatMap findBoolAfters xs
        | _ -> []

    /// Lifts a pair of before/after maps to a SubFun.
    let afterSubs asubs bsubs =
        { AVSub = function
                  | After a -> Map.tryFind a asubs |> withDefault (aAfter a)
                  | x -> AConst x
          BVSub = function
                  | After a -> Map.tryFind a bsubs |> withDefault (bAfter a)
                  | x -> BConst x }
        |> onVars

    /// Eliminates bound before/after pairs in the term.
    /// If x!after = f(x!before) in the action, we replace x!after with
    /// f(x!before) in the precondition and postcondition.
    let eliminateAfters term =
        let sub = afterSubs (term.Cmd |> findArithAfters |> Map.ofList)
                            (term.Cmd |> findBoolAfters |> Map.ofList)

        (* The substitution in term.Cmd will create a tautology
         * f(x!before) = f(x!before).
         * We assume we can eliminate it later.
         *)
        subExprInDTerm sub term

    (*
     * Guard reduction
     *)

    /// Return all known facts inside a conjunctive Boolean expression.
    let rec facts =
        function
        | BAnd xs -> concatMap facts xs
        | x -> [x]

    /// Reduce a Boolean expression, given some known facts.
    let rec reduce fs =
        function
        | x when Set.contains x fs -> BTrue
        | x when Set.contains (mkNot x) fs -> BFalse
        | BAnd xs -> mkAnd (List.map (reduce fs) xs)
        | BOr xs -> mkOr (List.map (reduce fs) xs)
        | BBEq (x, y) -> mkEq (reduce fs x |> BExpr) (reduce fs y |> BExpr)
        | BNot x -> mkNot (reduce fs x)
        | x -> x

    /// Reduce a GView, given some known facts.
    let reduceGView fs = mapConds (reduce fs) >> pruneGuardedSet

    /// Reduce the guards in a Term.
    let guardReduce {Cmd = c; WPre = w; Goal = g} =
        let fs = c |> facts |> Set.ofList
        {Cmd = c; WPre = reduceGView fs w; Goal = g}

    (*
     * Boolean simplification
     *)

    /// Performs expression simplification on a term.
    let simpTerm = subExprInDTerm { ASub = id; BSub = simp }

    (*
     * Frontend
     *)

    /// Term optimisers switched on by default.
    let defaultTermOpts =
        Set.ofList [ "term-remove-after"
                     "term-reduce-guards"
                     "term-simplify-bools" ]

    /// Optimises a model's terms.
    let optimise optR optA verbose =
        let optimiseTerm =
            Utils.optimiseWith optR optA verbose
                [ ("term-remove-after", true, eliminateAfters)
                  ("term-reduce-guards", true, guardReduce)
                  ("term-simplify-bools", true, simpTerm) ]
        mapAxioms optimiseTerm
