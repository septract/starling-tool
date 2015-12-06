/// The part of Starling that generates unreified terms from framed
/// axioms.
module Starling.TermGen

open Starling.Model
open Microsoft

/// Performs one step of a septraction of a GuarView.
let termGenSeptractStep model (rdone, qstep) rnext =
    let ctx = model.Context

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
    let rname = rnext.GView.VName
    let qname = qstep.GView.VName

    if rname = qname
    then
        let b1 = rnext.GCond
        let b2 = qstep.GCond
        let xbar = rnext.GView.VParams
        let xbar2 = qstep.GView.VParams

        // xbar = xbar'
        let xbarEq =
            ctx.MkAnd (Array.ofList <| List.map2 (curry ctx.MkEq) xbar xbar2)
            

        // B1 && !(B2 && xbar = xbar2)
        let rcond = ctx.MkAnd [|b1 ; ctx.MkNot (ctx.MkAnd [|b2 ; xbarEq|] ) |]
        let rnext2 = { rnext with GCond = rcond.Simplify () :?> Z3.BoolExpr }

        // B2 && !(B1 && xbar = xbar2)
        let qcond = ctx.MkAnd [|b2 ; ctx.MkNot (ctx.MkAnd [|b1 ; xbarEq|] ) |]
        let qstep2 = { qstep with GCond = qcond }

        (rnext2::rdone, qstep2)
    else (rnext::rdone, qstep)


/// Performs septraction of the single GuarView q from the GuarView
/// multiset r, returning r *- q.
let termGenSeptractView model r q =
    List.fold (termGenSeptractStep model) ([], q) r
    |> fst

/// Generates the septraction part of the weakest precondition.
let termGenSeptract model r q =
    (* We iterate on septraction of each item in q:
     * A *- (B * C) = (A *- B) *- C
     *)
    List.fold (termGenSeptractView model) r q

/// Generates a (weakest) precondition from a framed axiom.
let termGenPre model fax =
    (* Theoretically speaking, this is crunching an axiom {P} C {Q} and
     * frame view R into (P * (R *- Q)).
     * Remember that * is multiset union.
     * *- is trickier because we have guarded axioms, and is thus left
     * to termGenSeptract.
     *)
    List.append (fax.Axiom.Conditions.Pre)
                (termGenSeptract model fax.Frame fax.Axiom.Conditions.Post)

/// Generates a term from a framed axiom.
let termGenAxiom model fax =
    {TPre = termGenPre model fax
     TAction = fax.Axiom.Inner
     TPost = fax.Frame}

/// Generates a list of terms from a list of framed axioms.
let termGen (model: SemModel) = List.map (termGenAxiom model)
