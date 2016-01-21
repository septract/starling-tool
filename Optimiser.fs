/// Term optimiser for Starling.
module Starling.Optimiser

open Starling.Collections
open Starling.Expr
open Starling.Utils
open Starling.Model

(*
 * After elimination
 *)

/// Substitutes afters in a view func.
let subAftersInFunc sub func =
    {func with Params = List.map (subVars sub) func.Params}

/// Substitutes afters in a guarded view.
let subAftersInGuarded sub {Cond = c; Item = ms} =
    {Cond = boolSubVars sub c
     Item = subAftersInFunc sub ms}

/// Finds all instances of the pattern `x!after = f(x!before)` in a Boolean
/// expression that is either an equality or conjunction, and where x is arithmetic.
let rec findArithAfters =
    function
    | BAEq(AConst(After x), (ConstantArithFunction (Before y) as fx)) when x = y
        -> [(x, fx)]
    | BAEq(ConstantArithFunction (Before y) as fx, AConst(After x)) when x = y
        -> [(x, fx)]
    | BAnd xs -> concatMap findArithAfters xs 
    | _ -> []

/// Finds all instances of the pattern `x!after = f(x!before)` in a Boolean
/// expression that is either an equality or conjunction, and where x is Boolean.
let rec findBoolAfters =
    function
    | BBEq(BConst(After x), (ConstantBoolFunction (Before y) as fx)) when x = y
        -> [(x, fx)]
    | BBEq(ConstantBoolFunction (Before y) as fx, BConst(After x)) when x = y
        -> [(x, fx)]
    | BAnd xs -> concatMap findBoolAfters xs 
    | _ -> []

/// Lifts a pair of before/after maps to a SubFun.
let afterSubs asubs bsubs =
    { ASub = function
             | After a -> Map.tryFind a asubs |> withDefault (aAfter a)
             | x -> AConst x
      BSub = function
             | After a -> Map.tryFind a bsubs |> withDefault (bAfter a)
             | x -> BConst x }

/// Eliminates bound before/after pairs in the term.
/// If x!after = f(x!before) in the action, we replace x!after with f(x!before)
/// in the precondition and postcondition.
let eliminateAfters { WPre = p ; Goal = q ; Cmd = r } =
    let sub = afterSubs (r |> findArithAfters |> Map.ofList)
                        (r |> findBoolAfters |> Map.ofList)
                  
    { WPre = Multiset.map (subAftersInGuarded sub) p
      Goal = subAftersInFunc sub q
      (* This step will create a tautology f(x!before) = f(x!before).
       * We assume we can eliminate it later.
       *)
      Cmd = boolSubVars sub r }

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
 * Tautology, contradiction and identity collapsing
 *)

/// Performs tautology/contradiction/identity collapsing on a BoolExpr.
let rec tciCollapseBool =
    function
    | Tautology _ -> BTrue
    | Contradiction _ -> BFalse
    | Identity x -> tciCollapseBool x
    | x -> x

/// Performs tautology/contradiction/identity collapsing on an Expr.
let tciCollapseExpr =
    function
    | AExpr a -> a |> AExpr
    | BExpr b -> b |> tciCollapseBool |> BExpr

/// Performs tautology/contradiction/identity collapsing on a func.
let tciCollapseFunc {Name = n; Params = ps} =
    {Name = n; Params = List.map tciCollapseExpr ps}

/// Performs tautology/contradiction/identity collapsing on a GFunc.
let tciCollapseGFunc {Cond = c; Item = v} =
    {Cond = tciCollapseBool c; Item = tciCollapseFunc v}

/// Performs tautology/contradiction/identity collapsing on a GView.
let tciCollapseGView = Multiset.map tciCollapseGFunc

/// Performs tautology/contradiction/identity collapsing on a term.
let tciCollapse {Cmd = c; WPre = w; Goal = g} =
    {Cmd = tciCollapseBool c
     WPre = tciCollapseGView w
     Goal = tciCollapseFunc g}

(*
 * Frontend
 *)

/// Optimises a term individually.
/// (Or, it will, when finished.)
let optimiseTerm =
    // TODO(CaptainHayashi): add optimising passes.
    eliminateAfters
    >> guardReduce
    >> tciCollapse

/// Optimises a model's terms.
let optimise : Model<STerm<GView, VFunc>, DFunc> -> Model<STerm<GView, VFunc>, DFunc> =
    mapAxioms optimiseTerm
