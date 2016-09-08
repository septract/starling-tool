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
let reifySingleDef
  (protos : FuncDefiner<ProtoInfo>)
  view accumulator (dv : DView, _) =
    let rec matchMultipleViews
      (pattern : DView)
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
            // TODO(CaptainHayashi): this is a nasty hack.  Fix ASAP.
            let p =
                match (TermGen.Iter.lowerIterDFunc protos p) with
                | Chessie.ErrorHandling.Ok (pp, _) -> pp
                | _ -> failwith "FIXME: iterator dfunc lowering failed"

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
  (protos : FuncDefiner<ProtoInfo>)
  (definer : ViewDefiner<SVBoolExpr option>)
  (vap : IteratedGView<Sym<MarkedVar>>)
  : Set<GuardedIteratedSubview> =
    let goal = Multiset.toFlatList vap
    definer
    |> ViewDefiner.toSeq
    |> Seq.fold (reifySingleDef protos goal) Set.empty

/// Reifies all of the terms in a model's axiom list.
let reify
  (model : Model<Term<'a, IteratedGView<Sym<MarkedVar>>, OView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Model<Term<'a, Set<GuardedIteratedSubview>, OView>,
          ViewDefiner<SVBoolExpr option>> =
      mapAxioms (mapTerm id (reifyView model.ViewProtos model.ViewDefs) id) model
