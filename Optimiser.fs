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
    ///     Given a node, tries to unify every other node that is
    ///     equivalent and connected, but only by no-op commands, into it.
    /// </summary>
    /// <param name="removed">
    ///     The list of nodes already unified, which is appended to in the
    ///     result.
    /// </param>
    /// <param name="g">
    ///     The graph to unify (perhaps).
    /// </param>
    /// <param name="nName">
    ///     The name of the node to unify.
    /// </param>
    /// <returns>
    ///     A tuple containing the list of node names removed and a graph.
    ///     The graph is equivalent to <paramref name="g" />, but with some
    ///     nodes merged into <paramref name="nName" /> if they are
    ///     equivalent and connected only by no-op commands.
    /// </returns>
    let removeIdStep removed g nName =
        // First, find all of the other nodes that connect to this node.
        let nView, outNodes, inNodes = g.Contents.[nName]

        let outs = outNodes |> Set.toSeq |> Seq.map (fun { Dest = d } -> d)
        let ins = inNodes |> Set.toSeq |> Seq.map (fun { Src = s } -> s)

        Seq.append outs ins
        // Then, find out which ones are nop-connected.
        |> Seq.choose
               (fun xName ->
                    if (nopConnected g nName xName)
                    then (Some xName)
                    else None)
        (* If we found any nodes, then unify them.
         * We also have to wipe out the edges between both nodes.
         *)
        |> Seq.fold (fun (xs, gg) xName ->
                        // TODO(CaptainHayashi): make unify work on graphs
                        gg
                        |> rmEdgesBetween nName xName
                        |> rmEdgesBetween xName nName
                        |> unify nName xName
                        |> mkPair (xName :: xs))
                    (removed, g)

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
    let rec liftNodeOptimisation opt graph =
        // TODO(CaptainHayashi): do a proper depth-first search instead.

        let (xs, newGraph) =
            graph.Contents
            // Pull out nodeNames for removeIdStep.
            |> keys
            // Then, for each of those, try merging everything else into it.
            |> Seq.fold (uncurry opt) ([], graph)

        (* Tail-recurse back if we removed some nodes.
         * This is to see if we enabled more removals.
         *)
        if (Seq.isEmpty xs)
        then newGraph
        else liftNodeOptimisation opt newGraph

    /// <summary>
    ///     Merges equivalent nodes where they are connected, but only by
    ///     no-operations.
    /// </summary>
    /// <param name="_arg1">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     A graph equivalent to <paramref name="_arg1" />, but with all
    ///     equivalent nodes connected only by 'Id' merged.
    /// </returns>
    let removeIdTransitions = liftNodeOptimisation removeIdStep

    /// <summary>
    ///     Removes a node if it is an ITE-guarded view.
    ///
    ///     <para>
    ///         An ITE-guarded view is a view with one in-edge,
    ///         two guarded funcs which negate each other, and two
    ///         out-edges, each assuming one of the guards.
    ///     </para>
    /// </summary>
    /// <param name="removed">
    ///     The list of nodes already removed, which is appended to in the
    ///     result.
    /// </param>
    /// <param name="g">
    ///     The graph to optimise (perhaps).
    /// </param>
    /// <param name="nName">
    ///     The name of the node to optimise.
    /// </param>
    /// <returns>
    ///     A tuple containing the list of node names removed and a graph.
    ///     The graph is equivalent to <paramref name="g" />, but with
    ///     nodes merged into <paramref name="nName" />
    ///     equivalent and connected only by no-op commands.
    /// </returns>
    let removeITENodeStep removed g nName =
        // Does nName actually exist, and is it an ITE node?
        match (Map.tryFind nName g.Contents) with
        | Some (ITEGuards ({ Cond = xc },
                           { Cond = yc }), outEdges, inEdges) ->
            // Are there only two out edges, and only one in edges?
            if (Set.count outEdges = 2 && Set.count inEdges = 1)
            then
                let oE, iE = Set.toList outEdges, Set.toList inEdges
                let outA, outB = oE.[0], oE.[1]
                let inA : InEdge = iE.[0]

                (* Translate xc and yc to pre-state, because that's what
                 * the assumes will be.
                 *)
                let xcPre = (liftMarker Before always).BSub xc
                let ycPre = (liftMarker Before always).BSub yc

                // Are the out edges assumes over xc and yc?
                match (outA.Command, outB.Command) with
                | ([ { Name = aN ; Params = [ BExpr aP ] } ],
                   [ { Name = bN ; Params = [ BExpr bP ] } ])
                  when (aN = "Assume" && bN = "Assume"
                        && (equivHolds
                                (orEquiv
                                     (andEquiv (equiv aP xcPre)
                                               (equiv bP ycPre))
                                     (andEquiv (equiv aP ycPre)
                                               (equiv bP xcPre))))) ->
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
                    |> mkEdgeBetween (String.concat "__" [ inA.Name
                                                           outA.Name ])
                                     inA.Src
                                     outA.Dest
                                     (inA.Command @ outA.Command)
                    |> mkEdgeBetween (String.concat "__" [ inA.Name
                                                           outB.Name ])
                                     inA.Src
                                     outB.Dest
                                     (inA.Command @ outB.Command)
                    |> (mkPair removed')
                | _ -> (removed, g)
            else (removed, g)
        | _ -> (removed, g)

    /// <summary>
    ///     Optimises a graph.
    /// </summary>
    /// <param name="model">
    ///     The model whence the graph came.
    /// </param>
    /// <param name="_arg1">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="_arg1" />.
    /// </returns>
    let optimiseGraph model =
        // TODO(CaptainHayashi): Use the model for something.
        removeIdTransitions
        >> liftNodeOptimisation removeITENodeStep

    /// <summary>
    ///     Optimises a model over graphs.
    /// </summary>
    /// <param name="mdl">
    ///     The model to optimise.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="mdl" />.
    /// </returns>
    let optimise mdl =
        mapAxioms (optimiseGraph mdl) mdl


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

    /// Optimises a term individually.
    /// (Or, it will, when finished.)
    let optimiseTerm =
        eliminateAfters
        >> guardReduce
        >> simpTerm

    /// Optimises a model's terms.
    let optimise : Model<STerm<GView, VFunc>, DFunc>
                   -> Model<STerm<GView, VFunc>, DFunc> =
        mapAxioms optimiseTerm
