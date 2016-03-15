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
open Starling.Core.Model
open Starling.Core.Sub


/// <summary>
///     Graph optimisation.
/// </summary>
module Graph =
    open Starling.Core.Axiom
    open Starling.Core.Graph

    /// <summary>
    ///     Decides whether a program command is a no-op.
    /// </summary>
    /// <param name="cmd">
    ///     The command, as a <c>VFunc</c>.
    /// </param>
    /// <returns>
    ///     <c>true</c> if the command is a no-op;
    ///     <c>false</c> otherwise.
    /// </returns>
    let isNop (cmd : VFunc) =
        cmd.Params
        (* We treat a command func as a no-op if all variables it contains
         * are in the pre-state.  Thus, it cannot be modifying the
         * post-state, if it is well-formed.
         *)
        |> Seq.forall (function
                       | AExpr (AConst (Before _)) -> true
                       | AExpr (AConst _) -> false
                       | BExpr (BConst (Before _)) -> true
                       | BExpr (BConst _) -> false
                       | _ -> true)

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
    ///     A Chessie result.  If ok, it contains a tuple, containing the list
    ///     of node names removed and a graph.
    ///     The graph is equivalent to <paramref name="g" />, but with some
    ///     nodes merged into <paramref name="nName" /> " /> if they are
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
        |> seqBind (fun xName (xs, gg) ->
                        // TODO(CaptainHayashi): make unify work on graphs
                        gg
                        |> rmEdgesBetween nName xName
                        |> rmEdgesBetween xName nName
                        |> toSubgraph
                        |> fun sg -> (graph gg.Name (unify sg nName xName))
                        |> lift (mkPair (xName :: xs)))
                    (removed, g)

    /// <summary>
    ///     Merges equivalent nodes where they are connected, but only by 'Id'
    ///     transitions.
    ///
    ///     <para>
    ///         This assumes that 'Id' has the necessary semantics.
    ///     </para>
    /// </summary>
    /// <param name="graph">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     A graph equivalent to <paramref name="graph" />, but with all
    ///     equivalent nodes connected only by 'Id' merged.
    /// </returns>
    let rec removeIdTransitions graph =
        let result =
            graph.Contents
            // Pull out nodeNames for removeIdStep.
            |> keys
            // Then, for each of those, try merging everything else into it.
            |> seqBind
                   (fun k (rms, g) -> removeIdStep rms g k)
                   ([], graph)

        (* Tail-recurse back if we removed some nodes.
         * This is to see if we enabled more removals.
         *)
        match result with
        | Pass (xs, newGraph) when not (Seq.isEmpty xs) ->
              removeIdTransitions newGraph
        | x -> lift snd x

    /// <summary>
    ///     Optimises a graph.
    /// </summary>
    /// <param name="graph" />
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="graph" />.
    /// </returns>
    let optimiseGraph graph =
        graph
        |> removeIdTransitions

    /// <summary>
    ///     Optimises a model over graphs.
    /// </summary>
    /// <param name="mdl" />
    ///     The model to optimise.
    /// </param>
    /// <returns>
    ///     An optimised equivalent of <paramref name="mdl" />.
    /// </returns>
    let optimise mdl =
        tryMapAxioms optimiseGraph mdl


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

    /// Reduce a guard, given some known facts.
    let reduceGuarded fs {Cond = c; Item = i} =
        {Cond = reduce fs c; Item = i}

    /// Reduce a GView, given some known facts.
    let reduceGView fs =
        Multiset.map (reduceGuarded fs)

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
