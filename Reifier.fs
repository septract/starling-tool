/// <summary>
///     The part of the Starling process that performs the
///     backend-agnostic (in theory) part of reification.
/// </summary>
module Starling.Reifier

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Traversal
open Starling.Core.TypeSystem
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
        ///         <c>n</c>.  These two instances of the definition are called
        ///         <c>sdef</> and <c>bdef</c> below.
        ///     </para>
        /// </summary>
        | InductiveDownclosureError of view : DView * sdef : BoolExpr<Sym<Var>>
                                     * bdef : BoolExpr<Sym<Var>>
        /// <summary>
        ///     An iterated view definition failed the base downclosure
        ///     property with regards to the given definition of 'emp'.
        ///
        ///     <para>
        ///         This is the property that a view definition, when
        ///         instantiated with iterator <c>0</c>, is no stronger than
        ///         the definition for <c>emp</c> if any.
        ///     </para>
        /// </summary>
        | BaseDownclosureError of view : DView * def : BoolExpr<Sym<Var>>
                                * emp : BoolExpr<Sym<Var>>
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
        ///     An iterated func is being used in a non-iterated manner.
        /// </summary>
        | NoIteratorOnIterated of func : IteratedDFunc
        /// <summary>
        ///     An non-iterated func is being used in an iterated manner.
        /// </summary>
        | IteratorOnNonIterated of func : IteratedDFunc
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
        ///     A view occurred in a constraint that does not exist.
        ///
        ///     <para>
        ///         Usually this will be caught earlier on, but this is here
        ///         to make sure.
        ///     </para>
        /// </summary>
        | NoSuchView of func : DFunc
        /// <summary>
        ///     A view lookup failed during downclosure checking.
        ///
        ///     <para>
        ///         Usually this will be caught earlier on, but this is here
        ///         to make sure.
        ///     </para>
        /// </summary>
        | LookupError of func : DFunc * err : Core.Definer.Error
        /// <summary>
        ///     An iterator had the wrong type.
        /// </summary>
        | BadIteratorType of view : DView * ty : Type
        /// <summary>
        ///     An iterator was missing where there should have been one.
        /// </summary>
        | MissingIterator of view : DView
        /// <summary>
        ///     An expression traversal went belly-up.
        /// </summary>
        | Traversal of TraversalError<Error>


/// <summary>
///     Downclosure checking.
///
///     <para>
///         The presence of this in the reifier is a marriage of convenience.
///         Later, we might separate it.
///     </para>
/// </summary>
module Downclosure =
    open Starling.Core.ExprEquiv
    open Starling.Core.Traversal

    /// <summary>
    ///     Adapts Instantiate.lookup to the downclosure checker's needs.
    /// </summary>
    /// <param name="protos">The set of prototypes to look-up.</param>
    /// <param name="func">The func to look up in the definer.</param>
    /// <returns>
    ///     If the lookup was successful, a result containing the prototype info
    ///     of <paramref name="func"/> if it exists; an <see cref="Error"/>
    ///     otherwise.
    /// </returns>
    let lookupFunc (protos : FuncDefiner<ProtoInfo>) (func : DFunc)
      : Result<ProtoInfo option, Error> =
        // TODO(CaptainHayashi): merge with Modeller.lookupFunc?
        let look func = Core.Definer.FuncDefiner.lookup func protos
        let record = wrapMessages LookupError look func
        lift (Option.map snd) record

    /// <summary>Type of downclosure check results.</summary>
    type DownclosureResult =
        | /// <summary>Downclosure has been proven.</summary>
          Proven
        | /// <summary>Downclosure has been refuted.</summary>
          Refuted
        | /// <summary>Downclosure cannot be decided: reason given.</summary>
          Inconclusive of reason : string

    /// <summary>
    ///     Runs a downclosure check using Z3.
    /// </summary>
    /// <param name="check">The check to run.</param>
    /// <returns>
    ///     The result of the downclosure check.
    /// </returns>
    let runDownclosureCheck (check : BoolExpr<Sym<Var>>) : DownclosureResult =
        // Expression equivalence cannot handle symbols, so try remove them.
        // If we can't, then we just kick downclosure down to the backend.
        // TODO(CaptainHayashi): is it sound to approximate here?
        let removeResult =
            mapTraversal
                (removeSymFromBoolExpr id)
                (mkTypedSub normalRec check)
        match removeResult with
        // If check is a tautology, it will be equivalent to 'true'.
        | Pass r ->
            if equivHolds id (equiv BTrue r) then Proven else Refuted
        | _ -> Inconclusive "check is symbolic"

    /// <summary>
    ///     Checks the base downclosure property.
    ///     <para>
    ///         This states that, for all iterated views <c>A(x)[n]</c>,
    ///         <c>D(emp) => D(A(x)[0])</c>: their definitions are no stronger
    ///         than that of the empty view.  If there is no <c>D(emp)</c>, we
    ///         instead must prove <c>D(A(x)[0])</c> is a tautology.
    ///     </para>
    /// </summary>
    /// <param name="empDefn">The empty-view definition, <c>D(emp)</c>.</param>
    /// <param name="iterator">The iterator variable, <c>n</c>.</param>
    /// <param name="func">The iterated func to check, <c>A(x)[n]</c>.</param>
    /// <param name="defn">The definition to check, <c>D(A(x)[n])</c>.</param>
    /// <param name="deferred">The log of existing deferred checks.</param>
    /// <returns>
    ///     The original definition if base downclosure holds; an error
    ///     otherwise.
    /// </returns>
    let checkBaseDownclosure
      (empDefn : BoolExpr<Sym<Var>> option)
      (iterator : Var)
      (func : IteratedDFunc)
      (defn : BoolExpr<Sym<Var>>)
      (deferred : DeferredCheck list)
      : Result<DeferredCheck list, Error> =
        (* To do the base downclosure, we need to replace all instances of the
           iterator in the definition with 0. *)
        let baseDefnR =
             mapMessages Traversal
                (mapOverIteratorUses (fun _ -> IInt 0L) iterator defn)

        // If emp is indefinite (None), defer this base downclosure check.
        match empDefn with
        | None ->
            ok (NeedsBaseDownclosure (func, "emp is indefinite")::deferred)
        | Some ed ->
            (* Base downclosure for a view V[n](x):
                 D(emp) => D(V[0](x))
               That is, the definition of V when the iterator is 0 can be no
               stricter than the definition of emp.

               The definition of emp can only mention global variables, so it
               need not need to be freshened. *)
            let checkR = lift (mkImplies ed) baseDefnR
            let baseHoldsR = lift runDownclosureCheck checkR
            bind
                (fun baseHolds ->
                    match baseHolds with
                    | Proven -> ok deferred
                    | Refuted -> fail (BaseDownclosureError ([func], defn, ed))
                    | Inconclusive reason ->
                        ok (NeedsBaseDownclosure (func, reason)::deferred))
                baseHoldsR

    /// <summary>
    ///     Checks the inductive downclosure property.
    ///     <para>
    ///         This states that, for all iterated views <c>A(x)[n]</c>,
    ///         for all positive <c>n</c>, <c>D(A(x)[n+1]) => D(A(x)[n])</c>:
    ///         iterated view definitions must be monotonic over the iterator.
    ///         This, coupled with base downclosure, allows us to consider only
    ///         the highest iterator of an iterated func during reification,
    ///         instead of needing to take all funcs with an iterator less than
    ///         or equal to it.
    ///     </para>
    /// </summary>
    /// <param name="iterator">The iterator variable, <c>n</c>.</param>
    /// <param name="func">The iterated func to check, <c>A(x)[n]</c>.</param>
    /// <param name="defn">The definition to check, <c>D(A(x)[n])</c>.</param>
    /// <param name="deferred">The log of existing deferred checks.</param>
    /// <returns>
    ///     The original definition if inductive downclosure holds; an error
    ///     otherwise.
    /// </returns>
    let checkInductiveDownclosure (iterator : Var)
      (func : IteratedDFunc)
      (defn : BoolExpr<Sym<Var>>)
      (deferred : DeferredCheck list)
      : Result<DeferredCheck list, Error> =
        (* To do the inductive downclosure, we need to replace all instances of
           the iterator in the definition with (iterator + 1) in one version. *)
        let succDefnR =
            mapMessages Traversal
                (mapOverIteratorUses (Reg >> incVar) iterator defn)

        (* Inductive downclosure for a view V[n](x):
             (0 <= n && D(V[n+1](x)) => D(V[n](x)))
           That is, the definition of V when the iterator is n+1 implies the
           definition of V when the iterator is n, for all positive n. *)
        let checkR =
            lift
                (fun succDefn ->
                    mkImplies
                        (mkAnd2
                            (mkIntLe (IInt 0L) (IVar (Reg iterator)))
                            succDefn)
                        defn)
                succDefnR

        let indHoldsR = lift runDownclosureCheck checkR

        bind2
            (fun succDefn indHolds ->
                match indHolds with
                | Proven -> ok deferred
                | Refuted -> fail (InductiveDownclosureError ([func], succDefn, defn))
                | Inconclusive reason ->
                    ok (NeedsInductiveDownclosure (func, reason)::deferred))
            succDefnR
            indHoldsR

    /// <summary>
    ///     Checks the base and inductive downclosure properties on a given
    ///     arity-1 view definition.
    /// </summary>
    /// <param name="func">The view definition's lone defined func.</param>
    /// <param name="empDefn">The definition of 'emp', if one exists.</param>
    /// <param name="defn">The definition of <paramref name="func"/>.</param>
    /// <param name="deferred">The log of existing deferred checks.</param>
    /// <returns>
    ///     The set of deferred downclosure checks, if the non-deferred ones
    ///     passed; an error stating which property failed, otherwise.
    /// </returns>
    let checkDownclosure (func : IteratedDFunc)
        (empDefn : BoolExpr<Sym<Var>> option)
        (defn : BoolExpr<Sym<Var>> option)
        (deferred : DeferredCheck list)
        : Result<DeferredCheck list, Error> =
        let checkIterator =
            function
            | None -> fail (MissingIterator [func])
            | Some (Int (_, v)) -> ok v
            | Some v -> fail (BadIteratorType ([func], typeOf v))

        (* Delegate any checks on indefinite viewdefs to the backends, eg HSF
           and MuZ3, which must make sure their synthesised definitions are
           downclosed. *)
        match defn with
        | None ->
            ok
                (NeedsBaseDownclosure (func, "func is indefinite")
                :: NeedsInductiveDownclosure (func, "func is indefinite")
                :: deferred)
        | Some d ->
            let checkedIterR = checkIterator func.Iterator
            bind
                (fun checkedIter ->
                    let baseDeferredR =
                        checkBaseDownclosure empDefn checkedIter func d deferred
                    bind
                        (fun baseDeferred ->
                            checkInductiveDownclosure checkedIter func d
                                baseDeferred)
                        baseDeferredR)
                checkedIterR

    /// <summary>
    ///     Performs iterated view well-formedness checking on the left of a
    ///     view definition.
    /// </summary>
    /// <param name="empDefn">The definition, if any, of 'emp'.</param>
    /// <param name="vprotos">The view prototypes in use.</param>
    /// <param name="def">The definition being checked.</param>
    /// <param name="deferred">The log of existing deferred checks.</param>
    /// <returns>
    ///     The new deferred log if all testable checks passed;
    ///     errors otherwise.
    /// </returns>
    let checkDef
      (empDefn : BoolExpr<Sym<Var>> option)
      (vprotos : FuncDefiner<ProtoInfo>)
      (def : DView * BoolExpr<Sym<Var>> option)
      (deferred : DeferredCheck list)
      : Result<DeferredCheck list, Error> =
        let (lhs, rhs) = def

        (* First, we check the uses of the views in the lhs to see which
           are iterated in the definition. *)
        let iterprotos, normprotos =
            List.partition (fun func -> func.Iterator <> None) lhs

        (* Now, check that each iterated use matches up with an iterated
           prototype, and vice versa. *)
        let checkIterAgree shouldBeIterated error ifunc =
            let iInfoResult = lookupFunc vprotos ifunc.Func
            bind
                (function
                 | Some { IsIterated = ii } when ii = shouldBeIterated ->
                    ok ifunc
                 | Some _ -> fail (error ifunc)
                 | None -> fail (NoSuchView ifunc.Func))
                iInfoResult

        let iterProtoCheckedResult =
            collect (Seq.map (checkIterAgree true IteratorOnNonIterated) iterprotos)
        let normProtoCheckedResult =
            collect (Seq.map (checkIterAgree false NoIteratorOnIterated) normprotos)

        bind2
            (fun ips nps ->
                match (ips, nps) with
                (* Correct non-iterated view definition.
                   No more checking necessary. *)
                | [], _ -> ok deferred
                (* Correct iterated view definition, as long as i is actually an
                   iterated func.
                   Need to check inductive and base downclosure. *)
                | [i], [] ->
                    checkDownclosure i empDefn rhs deferred
                // Over-large iterated view definition (for now, anyway).
                | xs, [] -> fail (TooManyIteratedFuncs (lhs, List.length xs))
                // Mixed view definition (currently not allowed).
                | _, _ -> fail (MixedFuncType lhs))
            iterProtoCheckedResult
            normProtoCheckedResult

    /// <summary>
    ///     Performs all downclosure and well-formedness checking on iterated
    ///     constraints.
    /// </summary>
    /// <param name="vprotos">The view prototypes in use.</param>
    /// <param name="definer">
    ///     The definer whose constraints are being checked.
    /// </param>
    /// <param name="deferred">The log of existing deferred checks.</param>
    /// <returns>
    ///     The new deferred log if all testable checks passed;
    ///     errors otherwise.
    /// </returns>
    let check
      (vprotos : FuncDefiner<ProtoInfo>)
      (definer : ViewDefiner<BoolExpr<Sym<Var>> option>)
      (deferred : DeferredCheck list)
        : Result<DeferredCheck list, Error> =
        (* Get the definition of 'emp'.
           This is needed for base downclosure checking.

           There are three possibilities here:
           1) emp is defined, in which case we use the definition;
           2) emp is not defined, in which case we assume 'true' by the theory;
           3) emp is indefinite, in which case we pass None to 'checkDef' and
              'checkDef' then has to defer any base downclosure checks. *)
        let defSeq = ViewDefiner.toSeq definer
        let empDefIfDefined =
            Option.map snd (Seq.tryFind (fst >> List.isEmpty) defSeq)
        // Deal with case 2).
        let empDefn = withDefault (Some BTrue) empDefIfDefined

        // TODO (CaptainHayashi): actually use the result here
        seqBind (checkDef empDefn vprotos) deferred defSeq

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
///     <c>a==b, a==c, ...</c>.
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

    (* Have to make sure each class exists first; else exceptions happen.
       This is the role of icempty, which creates a map with each equivalence
       class present but empty. *)
    let emptyClasses = ifuncs |> Seq.map (fun name -> (name, [])) |> Map.ofSeq

    (* Now we collect into nlist the non-iterated funcs in the view, and
       simultaneously populate the empty equivalence classes such that each
       instance of a func with a specific name is collected into the same
       class. *)
    let nlist, iclasses =
        Multiset.fold expandFuncToReify ([], emptyClasses) view

    (* Now, go through the equivalence classes to calculate their case-split
       expansion.  We do this by working out every single possible set of
       equalities between the funcs in the class: say, for

       G1->A(a)[i] * G2->A(b)[j] * G3->A(c)[k]

       we have the cases (), (a=b), (a=c), (b=c), (a=b && a=c).  This turns out
       to be the powerset of the class, less the empty set, where each element
       of the powerset denotes equality between the members' parameters.
       We don't need the map keys at this stage. *)
    let iclassSeq = Map.toSeq iclasses
    let iclassPowersets = Seq.map (snd >> powerset) iclassSeq
    let ipsets = Seq.concat iclassPowersets

    (* Finally, we need to convert those equivalence powersets into a list of
       funcs. Each func represents an instance of one of the iterated funcs
       in the original view where a number of funcs sharing that name have
       been combined into one with the assertion that all of their parameters
       are the same. *)
    let mergeEqualitySet
      (mergedSoFar : IteratedGFunc<Sym<MarkedVar>> list)
      (equalitySet : IteratedGFunc<Sym<MarkedVar>> list) =
        match equalitySet with
        // Trivial cases first.
        | [] -> mergedSoFar
        | [func] -> func::mergedSoFar
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
            let iter = mkAdd (List.map (fun f -> f.Iterator) funcs)

            { Iterator = iter
              Func = { Cond = nguard; Item = (List.head funcs).Func }}
            :: mergedSoFar

    Seq.fold mergeEqualitySet nlist ipsets

/// Calculate the multiset of ways that this View matches the pattern in dv and
/// add to the accumulator.
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
                    (* How many times does a non-iterated pattern A(x) match an
                       func (G1->A(y)[n])?  (Note that the presence of an
                       iterator in that func does NOT necessarily make it an
                       iterated func: n could be 1, or 4, or 0, etc.)

                       Once, becoming (G1 && n>0 -> A(y)[1]).  We must then put
                       (G1 && n>0 -> A(y)[n-1]) back onto the view to match.

                       But what if n is always 0?  Then this pattern match
                       gets a false guard and, because we conjoin all the
                       pattern match guards above, it short-circuits to
                       false and kills off the entire view. *)

                    let nIsPos = mkIntGt v.Iterator (IInt 0L)
                    let func = { v.Func with Cond = mkAnd2 v.Func.Cond nIsPos }

                    let result =
                        { Func = func; Iterator = IInt 1L } :: result

                    let view =
                        { Func = func; Iterator = mkSub2 v.Iterator (IInt 1L) }
                        :: view

                    matchMultipleViews pattern (rview @ view) accumulator result
                | (Some n, true) ->
                    (* How many times does an ITERATED pattern A(x)[i] match the
                       func (G1 -> A(y)[n])?  As above, the answer is n.
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

/// <summary>
///     Reifies a given view using the given view prototypes and definer.
/// </summary>
/// <param name="protos">The view prototype definer in use.</param>
/// <param name="definer">The set of view definitions to reify against.</param>
/// <param name="view">The view to reify.</param>
/// <returns>
///     The set of all 'subviews' of the <paramref name="view"/>: views that
///     both match a constraint in <paramref name="definer"/> and are a
///     sub-multiset of <paramref name="view"/>, guarded by the conjunction of
///     all of the original guards of each func inside the subview as well as
///     any additional conditions for the pattern match to succeed.
/// </returns>
let reifyView
  (protos : FuncDefiner<ProtoInfo>)
  (definer : ViewDefiner<SVBoolExpr option>)
  (view : IteratedGView<Sym<MarkedVar>>)
  : Set<GuardedIteratedSubview> =
    let goal = preprocessView protos view
    definer
    |> ViewDefiner.toSeq
    |> Seq.fold (reifySingleDef protos goal) Set.empty

/// Performs sanity checking on the model, possibly producing deferred checks.
let sanityCheckModel
  (model : Model<Term<'a, IteratedGView<Sym<MarkedVar>>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Result<Model<Term<'a, IteratedGView<Sym<MarkedVar>>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>, Error> =
    // Currently the only sanity check is downclosure.
    let deferredCheckR =
        Downclosure.check
            model.ViewProtos
            model.ViewDefs
            model.DeferredChecks
    lift (fun ds -> { model with DeferredChecks = ds }) deferredCheckR

/// Reifies all of the terms in a model's axiom list.
let reify
  (model : Model<Term<'a, IteratedGView<Sym<MarkedVar>>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Result<Model<Term<'a, Set<GuardedIteratedSubview>, IteratedOView>,
                 ViewDefiner<SVBoolExpr option>>, Error> =
    let checkedModelR = sanityCheckModel model
    lift
        (mapAxioms (mapTerm id (reifyView model.ViewProtos model.ViewDefs) id))
        checkedModelR


/// <summary>
///     Pretty printers for the reifier types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.Traversal.Pretty

    /// <summary>
    ///     Pretty-prints an <see cref="Error"/>.
    /// </summary>
    let rec printError (err : Error) : Doc =
        match err with
        | InductiveDownclosureError (view, sdef, bdef) ->
            headed "Iterated view does not satisfy inductive downclosure property"
                [ errorInfo <|
                    headed "View being constrained"
                        [ printDView view ]
                  errorInfo <|
                    headed "Constraint failing inductive downclosure"
                        [ printBoolExpr (printSym printVar) bdef ]
                  headed "Constraint must be implied by the following"
                    [ errorInfo <| printBoolExpr (printSym printVar) sdef ] ]
        | BaseDownclosureError (view, def, emp) ->
            headed "Iterated view does not satisfy base downclosure property"
                [ errorInfo <|
                    headed "View being constrained"
                        [ printDView view ]
                  errorInfo <|
                    headed "Constraint failing base downclosure"
                        [ printBoolExpr (printSym printVar) def ]
                  headed "Constraint must be no stronger than 'emp' when \
                          iterator is zero"
                    [ errorInfo <| printBoolExpr (printSym printVar) emp ] ]
        | TooManyIteratedFuncs (view, count) ->
            fmt "constraint '{0}' contains {1} iterated funcs, but iterated \
                 definitions can only contain at most one"
                [ printDView view
                  String (sprintf "%i" count) ]
        | MixedFuncType view ->
            fmt "constraint '{0}' mixes iterated and non-iterated views"
                [ printDView view ]
        | NoSuchView name
            -> fmt "no view prototype for '{0}'" [ printDFunc name ]
        | LookupError(func, err) ->
            wrapped "lookup for view"
                (printDFunc func)
                (err |> Core.Definer.Pretty.printError)
        | NoIteratorOnIterated func ->
            errorStr "view"
            <+> quoted
                    (printIteratedContainer
                        printDFunc
                        (maybe Nop printTypedVar)
                        func)
            <+> errorStr "is iterated, but used as non-iterated in a constraint"
        | IteratorOnNonIterated func ->
            errorStr "view"
            <+> quoted
                    (printIteratedContainer
                        printDFunc
                        (maybe Nop printTypedVar)
                        func)
            <+> errorStr "is not iterated, but used as iterated in a constraint"
        | BadIteratorType (view, ty) ->
            fmt "iterator on constraint '{0}' is of type {1}, should be int"
                [ printDView view
                  printType ty ]
        | MissingIterator view ->
            fmt "constraint '{0}' should have an iterator, but does not"
                [ printDView view ]
        | Traversal err -> printTraversalError printError err
        |> error
