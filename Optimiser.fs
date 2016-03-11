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
    open Starling.Core.Graph

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
        // TODO(CaptainHayashi): do something here
        graph name subgraph

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
