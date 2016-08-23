/// <summary>
///     The part of the Starling process that performs the
///     backend-agnostic (in theory) part of reification.
/// </summary>
module Starling.Reifier

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView
open Starling.Core.Symbolic


/// Calculate the multiset of ways that this View matches the pattern in dv and add to the assumulator.
let reifySingleDef view accumulator (dv : DView, _) =
    let rec matchMultipleViews
      (pattern : DFunc list)
      (view : SMGFunc list) accumulator result =
        match pattern with
        | [] ->
                //Pull out the set of guards used in this match, and add to the set
                let guars, views =
                    result
                    |> List.map gFuncTuple
                    |> List.unzip
                Set.add
                    { // Then, separately add them into a ReView.
                    Cond = mkAnd guars
                    Item = List.rev views }
                    accumulator
        | p :: pattern ->
            let rec matchSingleView (view : SMGFunc list) rview accumulator =
               match view with
               | [] -> accumulator
               | v :: view ->
                  let accumulator =
                    if p.Name = v.Item.Name && p.Params.Length = v.Item.Params.Length then
                        matchMultipleViews pattern (rview @ view) accumulator (v::result)
                    else
                        accumulator
                  matchSingleView view (v :: rview) accumulator
            matchSingleView view [] accumulator

    matchMultipleViews dv view accumulator []

/// Reifies an dvs entire view application.
let reifyView
  (definer : ViewDefiner<SVBoolExpr option>)
  (vap : GView<Sym<MarkedVar>>)
  : Set<GuardedSubview> =
    let goal = Multiset.toFlatList vap
    definer
    |> ViewDefiner.toSeq
    |> Seq.fold (reifySingleDef goal) Set.empty

/// Reifies all of the terms in a model's axiom list.
let reify
  (model : Model<Term<'a, GView<Sym<MarkedVar>>, OView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Model<Term<'a, Set<GuardedSubview>, OView>,
          ViewDefiner<SVBoolExpr option>> =
      mapAxioms (mapTerm id (reifyView model.ViewDefs) id) model
