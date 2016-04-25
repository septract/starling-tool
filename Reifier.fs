/// The part of the Starling process that performs the backend-agnostic
/// (in theory) part of reification.
module Starling.Reifier

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView

/// Calculate the multiset of ways that this View matches the pattern in dv and add to the assumulator.
let reifySingleDef view accumulator (dv : SMBViewDef<DView>) = 

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
let reifyView (dvs : SMBViewDef<DView> List)  vap : SMViewSet = 
    let goal = Multiset.toFlatList vap
    Seq.fold (reifySingleDef goal) Set.empty dvs |> Multiset.ofFlatSeq

/// Reifies all of the views in a term.
let reifyTerm dvs = 
    (* For the goal, we need only calculate D(r), not |_r_|.
     * This means we need not do anything with the goal.
     *)
    mapTerm id (reifyView dvs) id

/// Reifies all of the terms in a model's axiom list.
let reify : UVModel<PTerm<SMGView, OView>> -> UVModel<PTerm<SMViewSet, OView>> =
    fun ms -> 
        mapAxioms (reifyTerm ms.ViewDefs) ms
