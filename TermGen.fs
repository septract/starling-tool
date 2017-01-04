/// <summary>
///     The part of Starling that generates unreified terms from framed
///     axioms.
/// </summary>
module Starling.TermGen

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Model
open Starling.Core.Command
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
let rec minusViewByFunc (qstep : IteratedGFunc<TermGenVar>)
  (r : IteratedGView<TermGenVar>)
  (rdone : IteratedGView<TermGenVar>)
  : IteratedGView<TermGenVar> =
    // Let qstep = (g2 -> w(ybar)^k).
    let { Func = { Cond = g2; Item = { Name = w; Params = ybar } }
          Iterator = k } = qstep

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
            let { Func = { Cond = g1; Item = { Name = v; Params = xbar } }
                  Iterator = n } = rstep

            (* If v <> w, then the two funcs are disjoint, minusing does
               nothing, and we continue to the next element in r with no
               modification to rstep or qstep. *)
            if v <> w
            then minusViewByFunc qstep rnext (Multiset.add rdone rstep)
            (* If g1 is trivially false, then rstep simplifies to emp,
               cannot be minused, and we continue as if rstep never existed. *)
            else if isFalse g1 then minusViewByFunc qstep rnext rdone
            else
                (* Otherwise, we apply the rewrite rule from the meta-theory:

                   ((g1 -> v(xbar)^n) * rnext) \ (g2 -> v(ybar)^k)
                   =   (g1 ^ g2 ^ xbar=ybar ^ n>k -> v(xbar)^n-k)       =rsucc
                     * (g1 ^ !(g2 ^ xbar=ybar)    -> v(xbar)^n)         =rfail
                     * ((rnext
                         \ (g2 ^ g1 ^ xbar=ybar ^ k>n -> v(ybar)^k-n))  =qsucc
                        \  (g2 ^ !(g1 ^ xbar=ybar)    -> v(ybar)^k)))   =qfail

                   Our first task is to decide what each guarded func
                   (rsucc, rfail, qsucc, qfail) is.  Each has a similar format,
                   which is captured by mkfunc. *)
                let mkfunc guard args iter =
                    iterated (gfunc guard v args) iter

                let barEq = List.map2 mkEq xbar ybar |> mkAnd

                let rSuccG = mkAnd [ g1; g2; barEq; mkIntGt n k ]
                let rSucc = mkfunc rSuccG xbar (mkSub2 n k)

                let rFailG = mkAnd [ g1; mkNot (mkAnd2 g2 barEq) ]
                let rFail = mkfunc rFailG xbar n

                let qSuccG = mkAnd [ g2; g1; barEq; mkIntGt k n ]
                let qSucc = mkfunc qSuccG ybar (mkSub2 k n)

                let qFailG = mkAnd [ g2; mkNot (mkAnd2 g1 barEq) ]
                let qFail = mkfunc qFailG ybar k

                (* Now, we have to minus qSucc and qFail from rnext.  The first
                   one is done in isolation (because eg. if we added rdone we'd
                   accidentally calculate rdone/qFail!), but we can optimise the
                   second one by passing through all the already-minused bits of
                   (rdone, rSucc, rFail) as the new rdone. *)

                // No need to check whether qSuccG/qFailG are trivially false:
                // it's the first thing we'll do in each recursive call.
                let innerMinus = minusViewByFunc qSucc rnext Multiset.empty

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
                    innerMinus
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
/// </param>
/// <returns>
///     The subtracted frame view.
/// </returns>
let termGenWPreMinus
  (r : IteratedOView)
  (q : IteratedGView<Sym<MarkedVar>>)
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
       which turns our job into a simple fold over Q. *)
    Multiset.fold
        (fun rSoFar qStep i ->
             minusViewByFunc (normalise qStep i) rSoFar Multiset.empty)
        rGuard
        q

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
                (tliftOverIteratedGFunc
                    (tliftOverExpr (traverseTypedSymWithMarker mark)))
                id)
        >> mapMessages Traversal

    let preResult = markView Before gax.Axiom.Pre
    let postResult = markView After gax.Axiom.Post
    let goal = gax.Goal

    lift2 (fun pre post -> Multiset.append pre (termGenWPreMinus goal post))
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

/// Stage that flattens the Iterator's from GuardedFunc's
module Iter =
    open Starling.Core.Instantiate

    /// <summary>
    ///     Type of errors that can occur during iterator lowering.
    /// </summary>
    type Error =
        /// <summary>
        ///     A func was lowered that doesn't have a valid prototype.
        /// </summary>
        | ProtoLookupError of FuncName : string
                            * Error : Starling.Core.Definer.Error
        /// <summary>
        ///     A func was lowered that doesn't have a prototype at all.
        /// </summary>
        | ProtoMissing of FuncName : string
        /// <summary>
        ///     A non-iterated func had a symbolic iterator.
        /// </summary>
        | CannotEvalIterator of Func : Func<Expr<Sym<MarkedVar>>>
                              * Iterator : IntExpr<Sym<MarkedVar>>

    /// <summary>
    ///     Pretty-prints an iterator lowering error.
    /// </summary>
    /// <param name="error">
    ///     The error to print.
    /// </param>
    /// <returns>
    ///     The <see cref="Doc"/> representing the error.
    /// </returns>
    let printError : Error -> Core.Pretty.Doc =
        function
        | ProtoLookupError (func, error) ->
            Core.Pretty.wrapped
                "prototype lookup for func"
                (Core.Pretty.String func)
                (Core.Definer.Pretty.printError error)
        | ProtoMissing func ->
            Core.Pretty.fmt
                "prototype missing for func '{0}'"
                [ Core.Pretty.String func ]
        | CannotEvalIterator (func, iterator) ->
            Core.Pretty.fmt
                "non-iterated func '{0}' is used with iterator '{1}', which
                 cannot be resolved to an integer"
                [ Core.View.Pretty.printSMVFunc func
                  Core.Expr.Pretty.printIntExpr
                      (Core.Symbolic.Pretty.printSym
                           Core.Var.Pretty.printMarkedVar)
                      iterator ]

    /// <summary>
    ///     Decides whether a func should be interpreted as iterated by looking
    ///     at its prototype.
    /// </summary>
    /// <param name="protos">
    ///     The prototype definer used to check the iterated status.
    /// </param>
    /// <param name="func">
    ///     The func to check.
    /// </param>
    /// <returns>
    ///     Whether the func is iterated, wrapped in an error because lookup
    ///     in the prototypes can fail.
    /// </returns>
    let checkIterated
      (protos : FuncDefiner<ProtoInfo>)
      (func : Func<'Param>)
      : Result<bool, Error> =
            FuncDefiner.lookup func protos
            |> mapMessages (fun f -> ProtoLookupError (func.Name, f))
            |> bind
                (function
                 | None -> fail (ProtoMissing func.Name)
                 | Some (_, { IsIterated = isIterated }) -> ok isIterated)

    /// <summary>
    ///     Decides whether a func should be interpreted as iterated by looking
    ///     at its prototype, and then tries to calculate the number of times
    ///     it should be inserted into its parent view if not.
    /// </summary>
    /// <param name="protos">
    ///     The prototype definer used to check the iterated status.
    /// </param>
    /// <param name="func">
    ///     The func to check.
    /// </param>
    /// <param name="iterator">
    ///     The iterator expression that was attached to the func.  The presence
    ///     of this does not necessarily mean the func is supposed to be
    ///     iterated.  This is because previous stages can combine multiple
    ///     copies of a non-iterated func into one 'pseudo-iterated' func for
    ///     simplicity.
    /// </param>
    /// <returns>
    ///     None if the func is iterated (and should thus be lowered); Some n
    ///     if the func is not iterated (and should instead just be replicated
    ///     n times, where n was the value of the iterator).
    ///     Wrapped in an error because lookup in the prototypes, and
    ///     evaluating the func's iterator, can fail.
    /// </returns>
    let evalIteratorIfFuncNotIterated
      (protos : FuncDefiner<ProtoInfo>)
      (func : Func<Expr<Sym<MarkedVar>>>)
      (iterator : IntExpr<Sym<MarkedVar>>)
      : Result<int64 option, Error> =
        func
        |> checkIterated protos
        |> bind
            (function
             | true -> ok None
             | false ->
                // TODO(CaptainHayashi): evaluate this properly.
                match iterator with
                | IInt n -> ok (Some n)
                | i -> fail (CannotEvalIterator (func, i)))

    /// <summary>
    ///     Lowers an iterated DFunc, folding it into an accumulating view.
    ///     <para>
    ///         If the func matches an iterated prototype, we move the Iterator
    ///         Expression into the params; else, we try to expand it.
    ///     </para>
    /// </summary>
    let lowerIterDFunc
      : FuncDefiner<ProtoInfo> -> IteratedDFunc -> Result<DFunc, Error> =
        fun protos { Func = dfunc; Iterator = it } ->
            dfunc
            |> checkIterated protos
            |> lift
                (function
                 // TODO(CaptainHayashi): assuming n here is silly
                 | true -> func dfunc.Name (withDefault (Int (normalRec, "n")) it :: dfunc.Params)
                 | false -> dfunc)

    /// <summary>
    ///     Lowers an iterated SMVFunc into a list of SMVFuncs.
    ///     <para>
    ///         If the func matches an iterated prototype, we move the Iterator
    ///         Expression into the params; else, we try to expand it.
    ///     </para>
    /// </summary>
    let lowerIterSMVFunc
      : FuncDefiner<ProtoInfo>
      -> IteratedContainer<Func<Expr<Sym<MarkedVar>>>, IntExpr<Sym<MarkedVar>>>
      -> Result<Func<Expr<Sym<MarkedVar>>> list, Error> =
        fun protos { Func = vfunc; Iterator = it } ->
            evalIteratorIfFuncNotIterated protos vfunc it
            |> lift
                (function
                 | Some k -> [ for i in 1L .. k -> vfunc ]
                 | None ->
                    [ func vfunc.Name (Int (normalRec, it) :: vfunc.Params) ])

    /// flattens an entire IteratedSubview into a flat GView
    let lowerIteratedSubview
      : FuncDefiner<ProtoInfo>
      -> GuardedIteratedSubview -> Result<GuardedSubview, Error> =
        fun protos { Cond = c; Item = iterview } ->
            iterview
            |> List.map (lowerIterSMVFunc protos)
            |> collect
            |> lift (List.concat >> (fun m -> { Cond = c; Item = m }))

    /// flattens an entire IteratedOView into a flat OView
    /// with no iterators
    let lowerIteratedOView : FuncDefiner<ProtoInfo> -> IteratedOView
      -> Result<OView, Error> =
        fun protos iteroview ->
            iteroview
            |> List.map (lowerIterSMVFunc protos)
            |> collect
            |> lift List.concat

    /// Flattens both the W/Pre and the Goal of a Term, removing the Iterators
    /// and returning the new flattened Term
    let lowerIteratedTerm :
      FuncDefiner<ProtoInfo>
      -> Term<_, Set<GuardedIteratedSubview>, IteratedOView>
      -> Result<Term<_, Set<GuardedSubview>, OView>, Error> =
        fun proto ->
            let lowerIteratedSubviewSet =
                Set.toSeq
                >> Seq.map (lowerIteratedSubview proto)
                >> collect
                >> lift Set.ofSeq

            tryMapTerm ok (lowerIteratedSubviewSet) (lowerIteratedOView proto)

    /// Flattens iterated guarded views in a model's terms down to guarded views
    /// taking iter[n] g(xbar...) to g(n, xbar...)
    /// and returning that new model
    let flatten
        (model : Model<Term<_, Set<GuardedIteratedSubview>, IteratedOView>, _>)
            : Result<Model<Term<_, Set<GuardedSubview>, OView>, _>, Error> =
        tryMapAxioms (lowerIteratedTerm model.ViewProtos) model
