/// The part of the Starling process that performs the backend-agnostic
/// (in theory) part of reification.
module Starling.Reifier

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Tries to look up a multiset View in the defining views dvs.
let findDefOfView dvs uviewm =
    // Why we do this is explained later.
    let uview = Multiset.toList uviewm
    (* We look up view-defs based on count of views and names of each
     * view in the def.
     *
     * Of course, this depends on us having ensured that there are no
     * errors in the view or its definition earlier.
     *)
    List.tryFind (fun {CViews = vdm} ->
        (* We need to do list operations on the multiset contents,
         * so convert both sides to a (sorted) list.  We rely on the
         * sortedness to make the next step sound.
         *)
        let vd = Multiset.toList vdm
        (* Do these two views have the same number of terms?
         * If not, using forall2 is an error.
         *)
        List.length vd = List.length uview && List.forall2 (fun d s -> d.Name = s.Name) vd uview) dvs

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

/// Reifies all of the terms in a model's axiom list.
let reify m = mapAxioms reifyTerm m
