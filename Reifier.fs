/// The part of the Starling process that performs the backend-agnostic
/// (in theory) part of reification.
module Starling.Reifier

open Microsoft

open Starling.Z3
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Converts a GuarView to a tuple.
let tupleOfGuarView gv = (gv.GCond, gv.GItem)

/// Reifies a single GuarView-list into a ReView.
let reifySingle model view =
    let ctx = model.Context

    (* This corresponds to Dlift in the theory.
     * Our end goal is the term (implies (and guars...) vrs),
     * where vrs is defined below.
     *)

    // First, pull the guards and views out of the view.
    let guars, views =
        view
        |> List.map tupleOfGuarView
        |> List.unzip

    // Then, separately add them into a ReView.
    {GCond = mkAnd ctx guars
     GItem = views}

/// Produces the power-multiset of a multiset (list).
let powermultiset ms =
    (* Solve the problem using Boolean arithmetic on the index of the
     * powerset item.
     *)
    seq {for i in 0 .. (1 <<< List.length ms) - 1 do
             yield (seq {0 .. (List.length ms) - 1}
                    |> Seq.choose (fun j ->
                                       let cnd: int = i &&& (1 <<< j)
                                       if cnd <> 0
                                       then Some ms.[j]
                                       else None)) |> List.ofSeq}
                                       
    |> Set.ofSeq



/// Reifies an entire view application.
let reifyView model vapp =
    vapp
    |> powermultiset
    |> Seq.map (List.ofSeq >> reifySingle model)
    |> Seq.toList

/// Reifies all of the views in a term.
let reifyTerm model term =
    let tpre = reifyView model term.Conditions.Pre
    let tpost = [reifySingle model term.Conditions.Post]

    {Conditions = {Pre = tpre
                   Post = tpost}
     Inner = term.Inner}

/// Reifies all of the terms in a term list.
let reify model = List.map (reifyTerm model)
