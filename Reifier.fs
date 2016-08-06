/// <summary>
///     The part of the Starling process that performs the
///     backend-agnostic (in theory) part of reification.
/// </summary>
module Starling.Reifier

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView
open Starling.Core.Symbolic
open Starling.Core.Var


/// Calculate the multiset of ways that this View matches the pattern in dv and add to the assumulator.
let reifySingleDef view accumulator (dv : SVBViewDef<DView>) =
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

    matchMultipleViews (viewOf dv) view accumulator []

/// Reifies an dvs entire view application.
let reifyView (dvs : SVBViewDef<DView> List) (vap : GView<Sym<MarkedVar>>)
  : Set<GuardedSubview> =
    let goal = Multiset.toFlatList vap
    Seq.fold (reifySingleDef goal) Set.empty dvs

/// Reifies all of the views in a term.
let reifyTerm dvs =
    (* For the goal, we need only calculate D(r), not |_r_|.
     * This means we need not do anything with the goal.
     *)
    mapTerm id (reifyView dvs) id

/// Reifies all of the terms in a model's axiom list.
let reify
  (model : Model<Term<'a, SMGView, OView>, ViewToSymBoolDefiner>)
  : Model<Term<'a, Set<GuardedSubview>, OView>, ViewToSymBoolDefiner> =
      mapAxioms (reifyTerm model.ViewDefs) model
