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
                |> List.map (fun f -> withDefault (AInt 1L) f.Iterator)
                |> List.fold mkAdd2 (AInt 0L)

            { Iterator = Some iter
              Func = { Cond = nguard; Item = (List.head funcs).Func }}
            :: xs

    Seq.fold mergeEqualitySet nlist ipsets

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
              Because the pattern is basically existential on x, and we
              preprocessed the view such that every possible thing it can match
              is inside the view, we can just case split on matching each
              iteration wholesale. *)
        | { Iterator = Some x; Func = p } :: pattern ->
            let rec matchSingleItView (view : IteratedGFunc<Sym<MarkedVar>> list) rview accumulator =
               match view with
               | [] -> accumulator
               | v :: view ->
                  let accumulator =
                    if p.Name = v.Func.Item.Name && p.Params.Length = v.Func.Item.Params.Length then
                        (* How many times does an iterated func A(x)[i]
                           iterated func A(y)[n]?  As above, all of them.
                           Thus, no remnant is put onto the view, and the entire
                           func is put onto the result. *)
                        let result = v :: result

                        (* We also now match against all of the funcs we
                           refused earlier (rview). *)
                        matchMultipleViews pattern (rview @ view) accumulator result
                    else
                        // The view doesn't match, so this match is dead.
                        accumulator
                  (* Now consider the case where we didn't choose the match.
                     This function now goes onto the set of refused funcs that
                     are placed back into any match we do choose. *)
                  matchSingleItView view (v :: rview) accumulator
            matchSingleItView view [] accumulator

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
  : Model<Term<'a, Set<GuardedIteratedSubview>, IteratedOView>,
          ViewDefiner<SVBoolExpr option>> =
      mapAxioms (mapTerm id (reifyView model.ViewProtos model.ViewDefs) id) model
