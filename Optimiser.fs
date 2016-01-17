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

/// Substitutes afters in a view multiset.
let subAftersInView sub =
    Multiset.map (subAftersInFunc sub)

/// Substitutes afters in a guarded view.
let subAftersInGuarded sub {Cond = c; Item = ms} =
    {Cond = boolSubVars sub c
     Item = subAftersInView sub ms}

/// Substitutes afters in a view assertion.
let subAftersInAssertion sub =
    Multiset.map (subAftersInGuarded sub)

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
                  
    { WPre = subAftersInAssertion sub p
      Goal = subAftersInAssertion sub q
      (* This step will create a tautology f(x!before) = f(x!before).
       * We assume we can eliminate it later.
       *)
      Cmd = boolSubVars sub r }

(*
 * Frontend
 *)

/// Optimises a term individually.
/// (Or, it will, when finished.)
let optimiseTerm =
    // TODO(CaptainHayashi): add optimising passes.
    eliminateAfters

/// Optimises a model's terms.
let optimise : Model<STerm<ViewSet>> -> Model<STerm<ViewSet>> =
    mapAxioms optimiseTerm
