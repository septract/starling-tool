/// <summary>
///     The part of Starling that generates unreified terms from framed
///     axioms.
/// </summary>
module Starling.TermGen

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Model
open Starling.Core.Axiom
open Starling.Core.Var

/// <summary>
///     Type of variables in funcs and views handled by TermGen.
/// </summary>
type TermGenVar = Sym<MarkedVar>

/// <summary>
///     Type of errors returned by the term generator.
/// </summary>
type Error =
    /// <summary>
    ///     An error occurred during traversal.
    ///     This error may contain nested semantics errors!
    /// </summary>
    | Traversal of TraversalError<Error>

/// <summary>
///     Normalises the iterator of an iterated func stored multiple times in a
///     view.
///     <para>
///         This converts <paramref name="i"/> copies of
///         <c>V(x)[n]</c> into one copy of <c>V(x)[n*i]</c>.
///     </para>
/// </summary>
/// <param name="func">
///     The <see cref="IteratedGFunc"/> to normalise.
/// </param>
/// <param name="i">
///     The number of times <paramref name="func"/> appears in its view.
/// </param>
/// <returns>
///     The normalised version of <paramref name="func"/> with respect to
///     <paramref name="i"/>.
/// </returns>
let normalise (func : IteratedGFunc<TermGenVar>) (i : int)
  : IteratedGFunc<TermGenVar> =
    mapIterator (fun x -> mkMul2 x (IInt (int64 i))) func

/// <summary>
///     Performs view minus of a view by a single func.
/// </summary>
/// <param name="qstep">
///     The func to subtract.
/// </param>
/// <param name="r">
///     The view to be subtracted from.
/// </param>
/// <param name="rdone">
///     A view to be merged with <paramref name="r"/> on termination.  This
///     usually carries the result of previous view minusing on a view of which
///     <paramref name="r"/> and <paramref name="rdone"/> are both part.
/// </param>
/// <returns>
///     The result of performing the view minus, merged with
///     <paramref name="rdone"/>.
/// </returns>
let rec minusViewByFunc (qstep : GFunc<TermGenVar>)
  (r : IteratedGView<TermGenVar>)
  (rdone : IteratedGView<TermGenVar>)
  : IteratedGView<TermGenVar> =
    // Let qstep = (g2 -> w(ybar)^k).
    let { Cond = g2; Item = w } = qstep
    let ybar = w.Params

    // If g2 is never true, then _nothing_ in r can ever be minused by it.
    if isFalse g2 then Multiset.append r rdone
    else
        // Base case: r is emp; inductive case: r is rstep+rnext.
        match Multiset.pop r with
        | None -> rdone
        | Some (rstepU, rnext, i) ->
            // Turn i copies of rstepU into a single func.
            let rstep = normalise rstepU i

            // Let rstep = (g1 -> v(xbar)^n),
            let { Func = { Cond = g1; Item = v }; Iterator = n } = rstep
            let xbar = v.Params

            (* If v <> w, then the two funcs are disjoint, minusing does
               nothing, and we continue to the next element in r with no
               modification to rstep or qstep. *)
            if v.Name <> w.Name
            then minusViewByFunc qstep rnext (Multiset.add rdone rstep)
            (* If g1 is trivially false, then rstep simplifies to emp,
               cannot be minused, and we continue as if rstep never existed. *)
            else if isFalse g1 then minusViewByFunc qstep rnext rdone
            else
                (* Otherwise, we apply the rewrite rule from the meta-theory.
                   This leaves us with three guarded funcs
                   (rsucc, rfail, qfail).  Each 'fail' func turns on if the
                   minus failed; the 'rsucc' func turns on if it succeeded.
                   Each has a similar format,
                   which is captured by mkfunc. *)
                let mkfunc guard args iter =
                    iterated
                        { Cond = guard
                          Item = Func.updateParams v args }
                        iter
                
                (* This is the 'equality guard', that tells us when the
                   r and q funcs actually match. *)
                let barEqG = List.map2 mkEq xbar ybar |> mkAnd

                (* Do we have a remainder?
                   If n = 1, then the minus eliminates r and we needn't
                   (and shouldn't) carry it around anymore.
                   If n = 0, r never existed.
                   Otherwise, we minus one from r. *) 
                let hasRemainderG = mkIntGt n (IInt 1L)

                (* This func represents any remainder. *)
                let rSuccG = mkAnd [ g1; g2; barEqG; hasRemainderG ]
                let rSucc = mkfunc rSuccG xbar (mkDec n)

                (* This func makes 'r' reappear if the minus failed.
                   (If the minus failed due to 'r' having iterator 0,
                   this func disappears regardless, so we don't check that
                   in the guard.) *)
                let rFailG = mkAnd [ g1; mkNot (mkAnd2 g2 barEqG) ]
                let rFail = mkfunc rFailG xbar n

                (* We don't have a remainder for 'q'.
                   Why not?  Because, if the subtraction succeeded,
                   then all 1 atoms in 'q' must have been used up in the
                   subtraction.

                   A previous version of this algorithm got this wrong, and
                   failed to terminate! *)

                (* To work out whether we carry over 'q' to the next atom,
                   we *do* need to take into consideration whether the minus
                   failed due to 'r' not existing. *)
                let rExistsG = mkIntGt n (IInt 0L)
                let qFailG = mkAnd [ g2; mkNot (mkAnd [g1; barEqG; rExistsG]) ]
                let qFail = { Cond = qFailG; Item = Func.updateParams v ybar }

                (* rSucc and rFail now get added to rdone for the tail call,
                   but we can optimise here by not doing so if their guards are
                   trivially false or their iterators are zero.

                   Iterators can become negative here, but the n>k guards
                   will always evaluate to false in this case, so they don't
                   ever make it past here. *)
                let optAdd rdoneSoFar rToAddG rToAdd =
                    if isFalse rToAddG || rToAdd.Iterator = IInt 0L
                    then rdoneSoFar
                    else Multiset.add rdoneSoFar rToAdd

                minusViewByFunc
                    qFail
                    rnext
                    (optAdd (optAdd rdone rSuccG rSucc) rFailG rFail)

/// <summary>
///     Generates the frame part of the weakest precondition.
///     <para>
///         In the meta-theory, this is <c>R \ Q</c>.
///     </para>
/// </summary>
/// <param name="r">
///     The view representing the goal to be subtracted from.
/// </param>
/// <param name="q">
///     The view representing the postcondition to subtract.
///     The postcondition never has any iterators, as non-constant
///     iterators can't be expressed.
/// </param>
/// <returns>
///     The subtracted frame view.
/// </returns>
let termGenWPreMinus
  (r : IteratedOView)
  (q : GView<Sym<MarkedVar>>)
  : IteratedGView<Sym<MarkedVar>> =
    (* Since R is unguarded and ordered at the start of the minus, we lift
       it to the guarded unordered view (forall f in R, (true -> Rn)). *)
    let rGuard =
        r
        |> List.map (mapIterated (fun f -> { Cond = BTrue; Item = f }))
        |> Multiset.ofFlatList

    (* We need to reduce the full multiset minus R \ Q
       into the easier minus ((G1 -> V1^n) * B) \ (G2 -> V2^k).  Part of
       this is done by minusViewByFunc, giving us the obligation to turn
       Q into a series of calls over a single func.  Thankfully, we have
       the law
         R \ (Qstep * Qrest) = (R \ Qstep) \ Qrest
       which turns our job into a simple fold over Q.
       
       NOTE: we fold over q as a sequence so as to fold over each
             func in q separately, rather than batching them up into
             equivalence classes as 'Multiset.fold' would do. *)
    Seq.fold
        (fun rSoFar qStep ->
             minusViewByFunc qStep rSoFar Multiset.empty)
        rGuard
        (Multiset.toFlatSeq q)

/// Folds a precondition into a normalised iterated view.
let iteratePre
  (pre : GView<Sym<MarkedVar>>)
  : IteratedGView<Sym<MarkedVar>> =
    Multiset.fold
        (fun ipre gfunc i ->
            Multiset.add ipre (iterated gfunc (IInt (int64 i))))
        Multiset.empty
        pre

/// Generates a (weakest) precondition from a framed axiom.
let termGenWPre
  (gax : GoalAxiom<'cmd>)
  : Result<IteratedGView<Sym<MarkedVar>>, Error> =
    (* Theoretically speaking, this is crunching an axiom {P} C {Q} and
     * goal view R into (P * (R \ Q)), where R \ Q is the weakest frame.
     * Remember that * is multiset append.
     * \ is trickier because we have guarded axioms, and is thus left
     * to termGenSeptract.
     *
     * At this stage, we also rename all constants in pre to their pre-state,
     * and those in post to their post-state.  This is sound because, at this
     * stage, both sides only contain local variables.
     *)
    let markView mark =
        mapTraversal
            (tchainM
                (tliftOverGFunc
                    (tliftOverExpr (traverseTypedSymWithMarker mark)))
                id)
        >> mapMessages Traversal

    let preResult = markView Before gax.Axiom.Pre
    let postResult = markView After gax.Axiom.Post
    let goal = gax.Goal

    lift2 (fun pre post -> Multiset.append (iteratePre pre) (termGenWPreMinus goal post))
        preResult
        postResult

/// Generates a term from a goal axiom.
let termGenAxiom (gax : GoalAxiom<'cmd>)
  : Result<Term<'cmd, IteratedGView<Sym<MarkedVar>>, IteratedOView>, Error> =
    lift (fun wpre -> { WPre = wpre; Goal = gax.Goal; Cmd = gax.Axiom.Cmd })
        (termGenWPre gax)

/// Converts a model's goal axioms to terms.
let termGen (model : Model<GoalAxiom<'cmd>, _>)
  : Result<Model<Term<'cmd, IteratedGView<Sym<MarkedVar>>, IteratedOView>, _>,
           Error> =
    tryMapAxioms termGenAxiom model


/// <summary>
///     Pretty printers for TermGen types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// <summary>
    ///     Pretty-prints term generator errors.
    /// </summary>
    /// <param name="err">The graph error to print.</param>
    /// <returns>
    ///     A pretty-printer command that prints <paramref name="err" />.
    /// </returns>
    let rec printError (err : Error) : Doc =
        match err with
        | Traversal err -> Starling.Core.Traversal.Pretty.printTraversalError printError err
