/// The part of the Starling process that performs the backend-agnostic
/// (in theory) part of reification.
module Starling.Reifier

open Microsoft
open Starling.Collections
open Starling.Z3
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Converts a GuarView to a tuple.
let tupleOfGuarView gv = (gv.GCond, gv.GItem)

/// Reifies a single GuarView-list into a ReView.
let reifySingle model view = 
    (* This corresponds to Dlift in the theory.
     * Our end goal is the term (implies (and guars...) vrs),
     * where vrs is defined below.
     *)

    // First, pull the guards and views out of the view.
    let guars, views = 
        view
        |> Multiset.map tupleOfGuarView
        |> Multiset.toList
        |> List.unzip
    { // Then, separately add them into a ReView.
      GCond = mkAnd model.Context guars
      GItem = Multiset.ofList views }

/// Reifies an entire view application.
let reifyView model = 
    Multiset.power
    >> Seq.map (reifySingle model)
    >> Multiset.ofSeq

/// Reifies all of the views in a term.
let reifyTerm model (term : Term) : ReTerm = 
    let tpre = reifyView model term.Conditions.Pre
    (* We need only calculate D(r), not |_r_|, so don't perform the
     * powersetting of the postcondition.
     *)
    let tpost = reifySingle model term.Conditions.Post |> Multiset.singleton
    { Conditions = 
          { Pre = tpre
            Post = tpost }
      Inner = term.Inner }

/// Reifies all of the terms in a term list.
let reify model = List.map (reifyTerm model)
