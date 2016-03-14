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
        // TODO(CaptainHayashi): generalise this, if sound to do so
        cmd.Name = "Id"

    /// <summary>
    ///     Unifies two given nodes in a subgraph if they are
    ///     equivalent and connected, but only by no-op commands.
    /// </summary>
    /// <param name="sg">
    ///     The graph to unify (perhaps).
    /// </param>
    /// <param name="x">
    ///     The first node to consider.
    /// </param>
    /// <param name="y">
    ///     The second node to consider.
    /// </param>
    /// <returns>
    ///     A subgraph equivalent to <paramref name="sg" />, but with
    ///     <paramref name="x" /> and <paramref name="y" /> merged if they are
    ///     equivalent and connected only by no-op commands.
    /// </returns>
    let removeIdStep sg x y =
        (* First, find out what the views on both sides are, and if they are
         * equal.
         * This lets us check x and y are actually both still in the graph.
         * Previous steps could have unified one or both of them away.
         *)
        match (Map.tryFind x sg.Nodes, Map.tryFind y sg.Nodes) with
        | (Some xv, Some yv) when xv = yv ->
            // Find the edges that map xv and yv.
            let xyEdges =
                Map.filter
                    (fun _ { Edge.Pre = p ; Edge.Post = q } ->
                         (p = x && q = y) || (p = y && q = x))
                    sg.Edges

            // Are all of the edges id?
            let allId =
                Map.forall (fun _ { Edge.Cmd = cmd } -> isNop cmd) xyEdges

            // If not, or the edge list is empty, leave the edges alone.
            if Map.isEmpty xyEdges || not allId
            then sg
            else
                // Delete the id nodes first, then unify the two nodes.
                let toKeep ename _ = not (Map.containsKey ename xyEdges)

                let sga =
                    { sg with Edges = Map.filter toKeep sg.Edges }
                unify sga x y
        | _ -> sg

    /// <summary>
    ///     Merges equivalent nodes where they are connected, but only by 'Id'
    ///     transitions.
    ///
    ///     <para>
    ///         This assumes that 'Id' has the necessary semantics.
    ///     </para>
    /// </summary>
    /// <param name="_arg1">
    ///     The graph to optimise.
    /// </param>
    /// <returns>
    ///     A graph equivalent to <paramref name="_arg1" />, but with all
    ///     equivalent nodes connected only by 'Id' merged.
    /// </returns>
    let removeIdTransitions { Name = name ; Contents = subgraph } =
        subgraph
        |> nodePairs
        |> Seq.fold (fun sg -> uncurry (removeIdStep sg))
           subgraph
        |> graph name

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
