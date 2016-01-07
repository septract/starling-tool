/// The part of the Starling process that performs the backend-agnostic
/// (in theory) part of reification.
module Starling.Reifier

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Converts a GuarView to a tuple.
let tupleOfGuarView {Cond = c; Item = i} = (c, i)

/// Reifies a single GuarView-list into a ReView.
let reifySingle view = 
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
      Cond = mkAnd guars
      Item = Multiset.ofList views }

/// Reifies an entire view application.
let reifyView vap = 
    vap
    |> Multiset.power
    |> Seq.map reifySingle
    |> Multiset.ofSeq

/// Reifies all of the views in a term.
let reifyTerm (term : Term) : ReTerm = 
    let tpre = reifyView term.Conditions.Pre
    (* We need only calculate D(r), not |_r_|, so don't perform the
     * powersetting of the postcondition.
     *)
    let tpost = reifySingle term.Conditions.Post |> Multiset.singleton
    { Conditions = 
          { Pre = tpre
            Post = tpost }
      Inner = term.Inner }

/// Reifies all of the terms in a term list.
let reify ts = List.map reifyTerm ts
