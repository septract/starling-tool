/// <summary>
///     The part of the Starling process that performs the
///     backend-agnostic (in theory) part of reification.
/// </summary>
module Starling.Reifier

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView
open Starling.Core.Symbolic
open Starling.TermGen.Iter

[<AutoOpen>]
module Types =
    /// <summary>
    ///     Errors that can be returned by the reifier.
    /// </summary>
    type Error =
        /// <summary>
        ///     An iterated view definition failed the inductive downclosure
        ///     property.
        ///
        ///     <para>
        ///         This is the property that, if a view definition holds for
        ///         a given iterator <c>n + 1</c>, it holds for the iterator
        ///         <c>n</c>.
        ///     </para>
        /// </summary>
        | InductiveDownclosureError of view : DView * def : BoolExpr<Sym<Var>>
        /// <summary>
        ///     An iterated view definition failed the base downclosure
        ///     property.
        ///
        ///     <para>
        ///         This is the property that a view definition, when
        ///         instantiated with iterator <c>0</c>, is no stronger than
        ///         the definition for <c>emp</c> if any.
        ///     </para>
        /// </summary>
        | BaseDownclosureError of view : DView * def : BoolExpr<Sym<Var>>
        /// <summary>
        ///     An iterated view definition contains more than one iterated
        ///     func.
        ///
        ///     <para>
        ///         This restriction is very conservative, and will probably
        ///         be relaxed in the future.
        ///     </para>
        /// </summary>
        | TooManyIteratedFuncs of view : DView * amount : int
        /// <summary>
        ///     A definition contains both iterated and non-iterated funcs.
        ///
        ///     <para>
        ///         This restriction is very conservative, and will probably
        ///         be relaxed in the future.
        ///     </para>
        /// </summary>
        | MixedFuncType of view : DView


/// <summary>
///     Downclosure checking.
///
///     <para>
///         The presence of this in the reifier is a marriage of convenience.
///         Later, we might separate it.
///     </para>
/// </summary>
module Downclosure =
    /// <summary>
    ///     Performs all downclosure and well-formedness checking on iterated
    ///     constraints.
    /// </summary>
    let check (definer : ViewDefiner<BoolExpr<Sym<Var>> option>)
        : Result<ViewDefiner<BoolExpr<Sym<Var>> option>, Error> =
        // TODO (CaptainHayashi): implement
        ok definer

/// Splits an iterated GFunc into a pair of guard and iterated func.
let iterGFuncTuple
  ({ Iterator = i; Func = { Cond = c; Item = f }} : IteratedGFunc<'Var>)
  : BoolExpr<'Var> * IteratedContainer<Func<Expr<'Var>>, IntExpr<'Var>> =
    (c, iterated f i)

/// <summary>
///     Generates the powerset of a set expressed as a list.
/// </summary>
/// <param name="xs">The set whose powerset is sought.</param>
/// <typeparam name="A">The type of set elements.</typeparam>
/// <returns>
///     The powerset of <paramref name="xs"/>, as a lazy sequence.
/// </returns>
let rec powerset (xs : 'A list) : 'A list seq =
    // originally by Tomas Petricek: see http://stackoverflow.com/a/16826554
    seq {
        match xs with
        | [] -> yield []
        | h::t -> for x in powerset t do yield! [x; h::x] }

/// <summary>
///     Given a series of iterated funcs
///     <c>A(a)[i] * A(b)[j] * A(c)[k] * ...</c>, generate the equalities
///     <c>i==j, i==k, ...</c>.
/// </summary>
/// <param name="flist">The NON-EMPTY list of funcs to generate over.</param>
/// <returns>The series of parameter equalities described above.</returns>
let paramEqualities (flist : IteratedFunc<Sym<MarkedVar>> list)
  : BoolExpr<Sym<MarkedVar>> list =
    let x = List.head flist
    concatMap
        (fun y -> List.map2 mkEq x.Func.Params y.Func.Params)
        (List.tail flist)

/// <summary>
///     Preprocesses a view for reification.
///
///     <para>
///         This function converts a view multiset into a list, and expands out
///         any case splits over potentially-equal iterated funcs:
///         for example, <c>(G1 -> A(x)[i]) * (G2 -> A(y)[j])</c> will also
///         generate the func <c>(G1 ^ G2 ^ x=y -> A(x)[i+j])</c> when
///         A(x) is iterated.
///     </para>
/// </summary>
/// <param name="protos">The prototypes used to find iterated funcs.</param>
/// <param name="view">The view to preprocess.</param>
/// <returns>The preprocessed view, as a func list.</returns>
let preprocessView
  (protos : FuncDefiner<ProtoInfo>)
  (view : IteratedGView<Sym<MarkedVar>>)
  : IteratedGFunc<Sym<MarkedVar>> list =
    (* First of all, find out which view prototypes are marked (i)terated,
       and which are (n)ot.  We assume func names are unique and all func
       references are well-formed (correct set of parameters), which should have
       been checked earlier. *)
    let ifuncs, nfuncs =
        protos
        |> FuncDefiner.toSeq
        |> Seq.fold
            (fun (is, ns) (func, pinfo) ->
                if pinfo.IsIterated
                then (Set.add func.Name is, ns)
                else (is, Set.add func.Name ns))
            (Set.empty, Set.empty)

    (* Now, go through the multiset's funcs.  Since the multiset may contain
       n copies of a k-iterated func, we normalise to one copy of a k*n-iterated
       func to get rid of the outer iterator.  What we then do depends on
       whether the func is iterated or not: if it isn't, we just emit it;
       otherwise, we add it to an equivalence class based on the func name so
       we can do the case-split expansion. *)
    let expandFuncToReify
      (ns, ic : Map<string, IteratedGFunc<Sym<MarkedVar>> list>) func n =
        let norm = TermGen.normalise func n
        let nname = norm.Func.Item.Name
        if ifuncs.Contains nname
        then (ns, Map.add nname (norm::ic.[nname]) ic)
        else (norm::ns, ic)

    // Have to make sure each class exists first; else exceptions happen.
    let icempty = ifuncs |> Seq.map (fun name -> (name, [])) |> Map.ofSeq
    let nlist, iclasses = Multiset.fold expandFuncToReify ([], icempty) view

    (* Now, go through the equivalence classes to calculate their case-split
       expansion.  We do this by working out every single possible set of
       equalities between the funcs in the class: say, for

       G1->A(a)[i] * G2->A(b)[j] * G3->A(c)[k]

       we have the cases (), (a=b), (a=c), (b=c), (a=b && a=c).  This turns out
       to be the powerset of the class, less the empty set, where each element
       of the powerset denotes equality between the members' parameters.
       We don't need the map keys at this stage. *)
    let ipsets : (IteratedGFunc<Sym<MarkedVar>> list) seq =
        iclasses |> Map.toSeq |> Seq.map (snd >> powerset) |> Seq.concat

    (* Finally, we need to convert those equivalence powersets into a list of
       funcs. *)
    let mergeEqualitySet xs =
        function
        // Trivial cases first.
        | [] -> xs
        | [func] -> func::xs
        (* Now we have a set of func G1->A(a)[i], G2->A(b)[j], G3->A(c)[k]...
           first, calculate the new guard G1^G2^G3^a=b^a=c^... *)
        | gfuncs ->
            let guards, funcs =
                gfuncs
                |> List.map iterGFuncTuple
                |> List.unzip
            let equalities = paramEqualities funcs
            let nguard = mkAnd (guards @ equalities)

            // And the new iterator i+j+k+...
            let iter =
                funcs
                |> List.map (fun f -> f.Iterator)
                |> List.fold mkAdd2 (AInt 0L)

            { Iterator = iter
              Func = { Cond = nguard; Item = (List.head funcs).Func }}
            :: xs

    Seq.fold mergeEqualitySet nlist ipsets

/// Calculate the multiset of ways that this View matches the pattern in dv and add to the assumulator.
let reifySingleDef
  (protos : FuncDefiner<ProtoInfo>)
  (view : IteratedGFunc<Sym<MarkedVar>> list)
  (accumulator : Set<GuardedIteratedSubview>)
  (dv : DView, _)
  : Set<GuardedIteratedSubview> =
    (* When we finish, we need to pull all of the guards out of the funcs
       we've matched, conjoin them, and use them to guard the iterated view
       the funcs now form.  These are then added to the accumulator. *)
    let mergeResults results accumulator =
        let guars, views = results |> List.map iterGFuncTuple |> List.unzip
        let cond = mkAnd guars

        if (isFalse cond)
        then accumulator
        else Set.add { Cond = cond; Item = List.rev views } accumulator

    (* First, we define what it means to match a view against a single pattern
       func p, given the rest of the pattern is in 'pattern'. *)
    let rec matchSingleView
      (p: IteratedDFunc)
      pattern
      (view : IteratedGFunc<Sym<MarkedVar>> list)
      rview
      accumulator
      result =
        match view with
        | [] -> accumulator
        | v :: view ->
            (* This pattern matches if, and only if, the funcs match. *)
            let pMatchesV =
                p.Func.Name = v.Func.Item.Name
                && p.Func.Params.Length = v.Func.Item.Params.Length

            (* Reification works by building up an accumulator of results from
               performing multiple possible pattern matches.  Because each
               single view match case-splits based on whether or not we take
               the match, we have to push lots of recursive match results into
               our own accumulator. *)
            let accumulator =
                match p.Iterator, pMatchesV with
                | (_, false) ->
                    // The view doesn't match, so this match is dead.
                    accumulator
                | (None, true) ->
                    (* How many times does a non-iterated func A(x) match an
                       iterated func (G1->A(y)[n])?  Once, becoming
                       (G1 && n>0 -> A(y)[1]).  We then have to put
                       (G1 && n>0 -> A(y)[n-1]) back onto the view to match.

                       But what if n is always 0?  Then this pattern match
                       gets a false guard and, because we conjoin all the
                       pattern match guards above, it short-circuits to
                       false and kills off the entire view. *)

                    let nIsPos = mkGt v.Iterator (AInt 0L)
                    let func = { v.Func with Cond = mkAnd2 v.Func.Cond nIsPos }

                    let result =
                        { Func = func; Iterator = AInt 1L } :: result

                    let view =
                        { Func = func; Iterator = mkSub2 v.Iterator (AInt 1L) }
                        :: view

                    matchMultipleViews pattern (rview @ view) accumulator result
                | (Some n, true) ->
                    (* How many times does an iterated func A(x)[i]
                       iterated func A(y)[n]?  As above, all of them.
                       Thus, no remnant is put onto the view, and the entire
                       func is put onto the result. *)
                    let result = v :: result

                    (* We also now match against all of the funcs we
                       refused earlier (rview). *)
                    matchMultipleViews pattern (rview @ view) accumulator result
            (* Now consider the case where we didn't choose the match.
               This function now goes onto the set of refused funcs that
               are placed back into any match we do choose. *)
            matchSingleView p pattern view (v :: rview) accumulator result
    (* We can now specify what it means to reify a view against an entire
       view pattern. *)
    and matchMultipleViews
      (pattern : DView)
      (view : IteratedGFunc<Sym<MarkedVar>> list) accumulator result =
        // TODO(CaptainHayashi): pattern vetting.
        match pattern with
        | [] -> mergeResults result accumulator
        (* Because we preprocessed the view, in both iterated and non-iterated
           cases we can simply traverse the view from left to right, and,
           every time we find something matching the pattern, split on whether
           we accept it.
           Run the case where we do and feed its results into the accumulator,
           then run the case where we don't with that accumulator. *)
        | p :: pattern -> matchSingleView p pattern view [] accumulator result

    matchMultipleViews dv view accumulator []

/// Reifies an dvs entire view application.
let reifyView
  (protos : FuncDefiner<ProtoInfo>)
  (definer : ViewDefiner<SVBoolExpr option>)
  (vap : IteratedGView<Sym<MarkedVar>>)
  : Set<GuardedIteratedSubview> =
    let goal = preprocessView protos vap
    definer
    |> ViewDefiner.toSeq
    |> Seq.fold (reifySingleDef protos goal) Set.empty

/// Reifies all of the terms in a model's axiom list.
let reify
  (model : Model<Term<'a, IteratedGView<Sym<MarkedVar>>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Result<Model<Term<'a, Set<GuardedIteratedSubview>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>, Error> =
    model
    |> mapAxioms (mapTerm id (reifyView model.ViewProtos model.ViewDefs) id)
    |> tryMapViewDefs Downclosure.check


/// <summary>
///     Pretty printers for the reifier types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty

    /// <summary>
    ///     Pretty-prints an <see cref="Error"/>.
    /// </summary>
    let printError : Error -> Doc =
        function
        | InductiveDownclosureError (view, def) ->
            fmt "definition of '{0}', {1}, does not satisfy inductive downclosure"
                [ printDView view
                  printBoolExpr (printSym printVar) def ]
        | BaseDownclosureError (view, def) ->
            fmt "definition of '{0}', {1}, does not satisfy base downclosure"
                [ printDView view
                  printBoolExpr (printSym printVar) def ]
        | TooManyIteratedFuncs (view, count) ->
            fmt "constraint '{0}' contains {1} iterated funcs, but iterated\
                 definitions can only contain at most one"
                [ printDView view
                  String (sprintf "%i" count) ]
        | MixedFuncType view ->
            fmt "constraint '{0}' mixes iterated and non-iterated views"
                [ printDView view ]
