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
open Starling.Core.Sub
open Starling.Core.GuardedView


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
    ///     Decides whether a program command is a no-op.
    /// </summary>
    /// <param name="_arg1">
    ///     The command, as a <c>Command</c>.
    /// </param>
    /// <returns>
    ///     <c>true</c> if the command is a no-op;
    ///     <c>false</c> otherwise.
    /// </returns>
    let isNop =
        List.forall
            (fun { Params = ps } ->
                 (* We treat a func as a no-op if all variables it contains
                  * are in the pre-state.  Thus, it cannot be modifying the
                  * post-state, if it is well-formed.
                  *)
                 Seq.forall (function
                             | AExpr (AConst (Before _)) -> true
                             | AExpr (AConst _) -> false
                             | BExpr (BConst (Before _)) -> true
                             | BExpr (BConst _) -> false
                             | _ -> true)
                            ps)

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
        let xView, xOut, xIn = graph.Contents.[x]
        let yView, _, _ = graph.Contents.[y]

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
    /// <param name="f">
    ///     The function, which takes:
    ///     the name of the node to look at for optimising;
    ///     the view of the node;
    ///     the out-edges of the node;
    ///     the in-edges of the node;
    ///     the graph to optimise;
    ///     and the list of edges removed from the node so far, to append
    ///     to if this optimisation removes nodes.
    ///
    ///     It should return the list of edges removed, the optimised
    ///     graph, and an Option containing the node name if the node has
    ///     not been removed.
    /// </param>
    /// <returns>
    ///     A new function, which takes and returns the edge-graph-node
    ///     triple <c>onNodes</c> expects.
    /// </returns>
    let expandNodeIn f =
        function
        | (rs, g, None) -> (rs, g, None)
        | (rs, g, Some n) ->
            match Map.tryFind n g.Contents with
            | Some (nV, outs, ins) -> f n nV outs ins g rs
            | None -> (rs, g, Some n)

    /// <summary>
    ///     Given a node, tries to unify every other node that is
    ///     equivalent and connected, but only by no-op commands, into it.
    /// </summary>
    /// <param name="_arg1">
    ///     A triple of:
    ///     the list of edges already removed, which is appended to in the
    ///     result;
    ///     the graph to optimise (perhaps);
    ///     an Option containing the name of the node to optimise.
    /// </param>
    /// <returns>
    ///     A triple containing the list of node names removed, a graph,
    ///     and the input node Option.
    ///     The graph is equivalent to <paramref name="g" />, but with some
    ///     nodes merged into the named node if they are
    ///     equivalent and connected only by no-op commands.
    /// </returns>
    let collapseNops =
        expandNodeIn <|
            fun nName nView outEdges inEdges g removed ->
                let outNodes = outEdges
                               |> Set.toSeq
                               |> Seq.map (fun { Dest = d } -> d)
                let inNodes = inEdges
                              |> Set.toSeq
                              |> Seq.map (fun { Src = s } -> s)

                Seq.append outNodes inNodes
                // Then, find out which ones are nop-connected.
                |> Seq.filter (nopConnected g nName)
                (* If we found any nodes, then unify them.
                 * We also have to wipe out the edges between both nodes.
                 *)
                |> Seq.fold (fun (xs, gg) xName ->
                                gg
                                |> rmEdgesBetween nName xName
                                |> rmEdgesBetween xName nName
                                |> unify nName xName
                                |> mkPair (xName :: xs))
                            (removed, g)
                |> fun (removed', g') -> (removed', g', Some nName)

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
    /// <param name="_arg1">
    ///     A triple of:
    ///     the list of nodes already removed, which is appended to in the
    ///     result;
    ///     the graph to optimise (perhaps);
    ///     an Option containing the name of the node to optimise.
    /// </param>
    /// <returns>
    ///     A triple containing the list of edge names removed, an
    ///     optimised graph, and an Option containing the node name if it was
    ///     not removed.
    /// </returns>
    let collapseITEs =
        expandNodeIn <|
            fun nName nView outEdges inEdges g removed ->
                match nView with
                | ITEGuards ({ Cond = xc }, { Cond = yc }) ->
                    // Are there only two out edges, and only one in edges?
                    if (Set.count outEdges = 2 && Set.count inEdges = 1)
                    then
                        let oE, iE = Set.toList outEdges, Set.toList inEdges
                        let outA, outB = oE.[0], oE.[1]
                        let inA : InEdge = iE.[0]

                        (* Translate xc and yc to pre-state, to match the
                           commands. *)
                        let xcPre = (liftMarker Before always).BSub xc
                        let ycPre = (liftMarker Before always).BSub yc

                        // Are the out edges assumes over xc and yc?
                        match (outA.Command, outB.Command) with
                        | ([ { Name = aN ; Params = [ BExpr aP ] } ],
                           [ { Name = bN ; Params = [ BExpr bP ] } ])
                            when (aN = "Assume" && bN = "Assume"
                                  && equivHolds <|
                                         orEquiv
                                             (andEquiv (equiv aP xcPre)
                                                       (equiv bP ycPre))
                                             (andEquiv (equiv aP ycPre)
                                                       (equiv bP xcPre))) ->
                            let removed' =
                                outA.Name :: outB.Name :: inA.Name :: removed

                            let aCmd = inA.Command @ outA.Command

                            g
                            // Remove the existing edges first.
                            |> rmEdgesBetween inA.Src nName
                            |> rmEdgesBetween nName outA.Dest
                            |> rmEdgesBetween nName outB.Dest
                            // Then, remove the node.
                            |> rmNode nName
                            // Then, add the new edges.
                            |> mkEdgeBetween (glueNames inA outA)
                                             inA.Src
                                             outA.Dest
                                             (inA.Command @ outA.Command)
                            |> mkEdgeBetween (glueNames inA outB)
                                             inA.Src
                                             outB.Dest
                                             (inA.Command @ outB.Command)
                            |> (fun g' -> removed', g', None)
                        | _ -> (removed, g, Some nName)
                    else (removed, g, Some nName)
                | _ -> (removed, g, Some nName)

    /// <summary>
    ///     Removes views in the middle of two local commands.
    /// </summary>
    /// <param name="locals">
    ///     The environment of local variables, used to determine whether
    ///     commands are local.
    /// </param>
    /// <param name="_arg1">
    ///     A triple of:
    ///     the list of edges already removed, which is appended to in the
    ///     result;
    ///     the graph to optimise (perhaps);
    ///     an Option containing the name of the node to optimise.
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
    let dropLocalMidView locals =
        expandNodeIn <|
            fun nName nView outEdges inEdges g removed ->
                (* Only continue if there is one edge in each direction.
                   This is a restriction of the original optimisation. *)
                match (Set.toList outEdges, Set.toList inEdges) with
                | ( [ outE ], [ inE ] )
                    when // Don't allow cycles
                         outE.Dest <> nName
                         && inE.Src <> nName
                         // Commands must be local.
                         && isLocalCommand locals outE.Command
                         && isLocalCommand locals inE.Command ->

                    let removed' = outE.Name :: inE.Name :: removed

                    let g' =
                        g
                        |> rmEdgesBetween inE.Src nName
                        |> rmEdgesBetween nName outE.Dest
                        |> rmNode nName
                        |> mkEdgeBetween (glueNames inE outE)
                                         inE.Src
                                         outE.Dest
                                         (inE.Command @ outE.Command)

                    (removed', g', None)
                | _ -> (removed, g, Some nName)

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

        let (xs, newGraph, _) =
            graph.Contents
            // Pull out nodeNames for removeIdStep.
            |> keys
            // Then, for each of those, try merging everything else into it.
            // TODO(CaptainHayashi): react when an optimisation kills a node?
            |> Seq.fold (fun (r, g, _) n -> opt (r, g, Some n))
                        ([], graph, None)

        (* Tail-recurse back if we removed some nodes.
         * This is to see if we enabled more removals.
         *)
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
