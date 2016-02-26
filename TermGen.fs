/// The part of Starling that generates unreified terms from framed
/// axioms.
module Starling.TermGen

open Starling.Expr
open Starling.Collections
open Starling.Sub
open Starling.Model
open Starling.Axiom

/// Performs one step of a septraction of a GuarView.
let termGenSeptractStep (rdone, qstep) rnext = 
    (* This is based on Matt Parkinson's schema:
     * [rdone * rnext@(B1, p xbar) * rrest] *- qstep@(B2, p xbar2)
     * = rdone2@[rdone * rnext2@(B1 && !(B2 && xbar = xbar2), p xbar)]
     *   * (rrest *- qstep2@(B2 && !(B1 && xbar = xbar2), p xbar2))
     *
     * We lift this over view names: if the view is different on both
     * sides, we instead have rdone2 = rdone * rnext, qstep2 = qstep
     *
     * Our return value is (rdone2, qstep2).
     *)
    let rname = rnext.Item.Name
    let qname = qstep.Item.Name
    if rname = qname then 
        let b1 = rnext.Cond
        let b2 = qstep.Cond
        let xbar = rnext.Item.Params
        let xbar2 = qstep.Item.Params
        // xbar = xbar'
        let xbarEq = List.map2 mkEq xbar xbar2 |> mkAnd 

        // B2 && !(B1 && xbar = xbar2)
        let qcond = 
            mkAnd [ b2
                    mkNot (mkAnd [ b1; xbarEq ]) ]
        
        let qstep2 = { qstep with Cond = qcond }
        
        // B1 && !(B2 && xbar = xbar2)
        let rcond = 
            mkAnd [ b1
                    mkNot (mkAnd [ b2; xbarEq ]) ]
        
        if isFalse rcond then 
            (rdone, qstep2)
        else
            let rnext2 = { rnext with Cond = rcond }
            (rnext2 :: rdone, qstep2)
    else (rnext :: rdone, qstep)

/// Performs septraction of the single GView q from the GView
/// multiset r, returning r *- q.
let termGenSeptractView r q = List.fold termGenSeptractStep ([], q) r |> fst

/// Guards a frame view with true.
let guard r = { Cond = BTrue; Item = r }

/// Generates the septraction part of the weakest precondition.
let termGenSeptract r q = 
    (* We iterate on septraction of each item in q:
     * A *- (B * C) = (A *- B) *- 
     *
     * Since r is unguarded at the start of the septraction, we lift it
     * to the guarded view (true|r).
     *)
    List.fold termGenSeptractView (List.map guard r) q

/// Generates a (weakest) precondition from a framed axiom.
let termGenPre fax = 
    (* Theoretically speaking, this is crunching an axiom {P} C {Q} and
     * frame view R into (P * (R *- Q)).
     * Remember that * is multiset union.
     * *- is trickier because we have guarded axioms, and is thus left
     * to termGenSeptract.
     *
     * At this stage, we also rename all constants in pre to their pre-state,
     * and those in post to their post-state.  This is sound because, at this
     * stage, both sides only contain local variables.
     *)
    // TODO(CaptainHayashi): don't call this septract
     // TODO(CaptainHayashi): use something better than lists.
    let pre =
        fax.Axiom.Pre
        |> subExprInGView (liftMarker Before always)
        |> Multiset.toList
    let post = 
        fax.Axiom.Post
        |> subExprInGView (liftMarker After always)
        |> Multiset.toList
    let frame = fax.Frame |> Multiset.toList
    List.append pre (termGenSeptract frame post) |> Multiset.ofList

/// Generates a term from a framed axiom.
let termGenAxiom fax = 
    { WPre = termGenPre fax
      Goal = fax.Frame
      Cmd = fax.Axiom.Cmd }

/// Converts a model's framed axioms to terms.
let termGen : Model<FramedAxiom, DView> -> Model<PTerm<GView, View>, DView> = mapAxioms termGenAxiom
