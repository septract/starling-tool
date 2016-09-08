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
open Starling.TermGen.Iter

/// Splits an iterated GFunc into a pair of guard and iterated func.
let iterGFuncTuple
  ({ Iterator = i; Func = { Cond = c; Item = f }} : IteratedGFunc<'Var>)
  : BoolExpr<'Var> * IteratedContainer<Func<Expr<'Var>>, IntExpr<'Var>> =
    (c, iterated f i)

/// Calculate the multiset of ways that this View matches the pattern in dv and add to the assumulator.
let reifySingleDef
  (protos : FuncDefiner<ProtoInfo>)
  (view : IteratedGFunc<Sym<MarkedVar>> list)
  accumulator (dv : DView, _) =
    let rec matchMultipleViews
      (pattern : DView)
      (view : IteratedGFunc<Sym<MarkedVar>> list) accumulator result =
        // TODO(CaptainHayashi): pattern vetting.
        match pattern with
        | [] ->
                //Pull out the set of guards used in this match, and add to the set
                let guars, views =
                    result
                    |> List.map iterGFuncTuple
                    |> List.unzip
                Set.add
                    { // Then, separately add them into a ReView.
                    Cond = mkAnd guars
                    Item = List.rev views }
                    accumulator
        (* Flat pattern:
              simply traverse the view from left to right, and, every time we
              find something matching the pattern, split on whether we accept
              it or not.  Run the case where we do and feed its results into
              the accumulator, then run the case where we don't with that
              accumulator. *)
        | { Iterator = None; Func = p } :: pattern ->
            // TODO(CaptainHayashi): if the iterator is None, we assume the
            // func 'p' is non-iterated.  This needs to turn into a check on
            // the view protos.
            let rec matchSingleView (view : IteratedGFunc<Sym<MarkedVar>> list) rview accumulator =
               match view with
               | [] -> accumulator
               | v :: view ->
                  let accumulator =
                    if p.Name = v.Func.Item.Name && p.Params.Length = v.Func.Item.Params.Length then
                        (* How many times does a non-iterated func A(x) match an
                           iterated func A(y)[n]?

                           Since A is non-iterated, we can assume that any view
                           Starling constructs contains A a finite, known
                           number of times.  Thus, what we do is evaluate the
                           iterator, try to peel 1 off it, and split on that. *)
                        let iter =
                            match v.Iterator with
                            | None -> 1L
                            | Some (AInt n) -> n
                            | Some _ -> failwith "expected to be able to eval this iterator"

                        if (iter > 0L)
                        then
                            (* We only matched against _one_ of the parts of
                               A(y)[n], so put A(y)[n-1] back on the list. *)
                            let view =
                                { Func = v.Func
                                  Iterator = Some (AInt (iter - 1L)) }
                                :: view

                            // And push A(y)[1] onto the result.
                            let result =
                                { Func = v.Func; Iterator = Some (AInt 1L) }
                                :: result

                            (* We also now match against all of the funcs we
                               refused earlier (rview). *)
                            matchMultipleViews pattern (rview @ view) accumulator result
                        else
                            // The iterator is 0, so this match is dead.
                            accumulator
                    else
                        // The view doesn't match, so this match is dead.
                        accumulator
                  (* Now consider the case where we didn't choose the match.
                     This function now goes onto the set of refused funcs that
                     are placed back into any match we do choose. *)
                  matchSingleView view (v :: rview) accumulator
            matchSingleView view [] accumulator
        (* Iterated pattern:
              ??? *)
        | { Iterator = Some x; Func = p } :: pattern ->
            failwith "unimplemented"

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
  (model : Model<Term<'a, IteratedGView<Sym<MarkedVar>>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Model<Term<'a, Set<GuardedIteratedSubview>, IteratedOView>,
          ViewDefiner<SVBoolExpr option>> =
      mapAxioms (mapTerm id (reifyView model.ViewProtos model.ViewDefs) id) model
