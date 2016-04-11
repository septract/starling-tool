/// <summary>
///     Module of types and functions for guarded views.
///
///     <para>
///         Guarded views are a Starling extension to the views in
///         Dinsdale-Young et al.
///
///         Starling uses guarded views to represent case splits in
///         views.  They consist of a func (<c>GFunc</c>) or view
///         (<c>GView</c>) annotated with a guard expression.
///         The func/view's presence in the proof is conditional on
///         that expression.
///     </para>
/// </summary>
module Starling.Core.GuardedView

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Model


/// <summary>
///     Guarded view types.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A guarded item.
    ///
    ///     <para>
    ///         The semantics is that the <c>Item</c> is to be taken as
    ///         present in its parent context (eg a view) if, and only if,
    ///         <c>Cond</c> holds.
    ///     </para>
    /// </summary>
    /// <typeparam name="item">
    ///     The type of the guarded item.
    /// </typeparam>
    type Guarded<'item> =
        { /// <summary>
          ///    The guard condition.
          /// </summary>
          Cond : BoolExpr
          /// <summary>
          ///    The guarded item.
          /// </summary>
          Item : 'item }

    (*
     * Shorthand for guarded items.
     *)

    /// <summary>
    ///     A guarded <c>VFunc</c>.
    /// </summary>
    type GFunc = Guarded<VFunc>

    /// <summary>
    ///     A guarded view.
    /// </summary>
    /// <remarks>
    ///     These are the most common form of view in Starling internally,
    ///     although theoretically speaking they are equivalent to Views
    ///     with the guards lifting to proof case splits.
    /// </remarks>
    type GView = Multiset<GFunc>

    /// <summary>
    ///     A multiset of guarded views, as produced by reification.
    /// </summary>
    type ViewSet = Multiset<Guarded<View>>


(*
 * Constructors.
 *)

/// <summary>
///     Creates a new <c>GFunc</c>.
/// </summary>
/// <param name="guard">
///     The guard on which the <c>GFunc</c> is conditional.
/// </param>
/// <param name="name">
///     The name of the <c>GFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>GFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>GFunc</c> with the given guard, name, and parameters.
/// </returns>
let gfunc guard name pars = { Cond = guard ; Item = func name pars }


(*
 * Single-guard active patterns.
 *)

/// <summary>
///     Active pattern matching on trivially true guards.
/// </summary>
let (|Always|_|) { Cond = c ; Item = i } =
    if isTrue c then Some i else None

/// <summary>
///     Active pattern matching on trivially false guards.
/// </summary>
let (|Never|_|) { Cond = c ; Item = i } =
    if isFalse c then Some i else None


(*
 * Multiple-guard active patterns.
 *)

/// <summary>
///     Active pattern matching on if-then-else guard multisets.
///
///     <para>
///         If-then-else guardsets contain two non-false guards, at least one
///         of which is equal to the negation of the other.
///     </para>
///
///     <para>
///         The active pattern returns the guard and view of the first ITE
///         guard, then the guard and view of the second.  The views are
///         <c>GView</c>s, but with a <c>BTrue</c> guard.
///     </para>
/// </summary>
let (|ITEGuards|_|) ms =
    match (Multiset.toFlatList ms) with
    | [ x ; y ] when (equivHolds (negates x.Cond y.Cond)) ->
        Some (x.Cond, Multiset.singleton { Cond = BTrue; Item = x.Item },
              y.Cond, Multiset.singleton { Cond = BTrue; Item = y.Item })
    // {| G -> P |} is trivially equivalent to {| G -> P * ¬G -> emp |}.
    | [ x ] ->
        Some (x.Cond, Multiset.singleton { Cond = BTrue; Item = x.Item },
              mkNot x.Cond, Multiset.empty)
    | _ -> None

(*
 * Destructuring and mapping.
 *)

/// <summary>
///     Converts a <c>GFunc</c> to a tuple.
/// </summary>
/// <param name="_arg1">
///     The <c>GFunc</c> to destructure.
/// </param>
/// <returns>
///     The tuple <c>(c, i)</c>, where <c>c</c> is the guard condition
///     of <paramref name="_arg1" />, and <c>i</c> its item.
/// </returns>
let gFuncTuple { Cond = c ; Item = i } = (c, i)

/// <summary>
///     Maps over the condition of a guard.
/// </summary>
/// <param name="f">
///     The function to map over the <c>BoolExpr</c> guard condition.
/// </param>
/// <param name="_arg1">
///     The <c>Guarded</c> over which we are mapping.
/// </param>
/// <returns>
///     The new <c>Guarded</c> resulting from the map.
/// </returns>
let mapCond f { Cond = c ; Item = i } = { Cond = f c ; Item = i }

/// <summary>
///     Maps over the item of a guard.
/// </summary>
/// <param name="f">
///     The function to map over the guarded item.
/// </param>
/// <param name="_arg1">
///     The <c>Guarded</c> over which we are mapping.
/// </param>
/// <returns>
///     The new <c>Guarded</c> resulting from the map.
/// </returns>
let mapItem f { Cond = c ; Item = i } = { Cond = c ; Item = f i }

/// <summary>
///     Maps over the conditions of a guarded multiset (eg view).
/// </summary>
/// <param name="f">
///     The function to map over the <c>BoolExpr</c> guard conditions.
/// </param>
/// <param name="_arg1">
///     The multiset of <c>Guarded</c>s over which we are mapping.
/// </param>
/// <returns>
///     The multiset of <c>Guarded</c>s resulting from the map.
/// </returns>
let mapConds f = Multiset.map (mapCond f)

/// <summary>
///     Maps over the internal items of a guarded multiset (eg view).
/// </summary>
/// <param name="f">
///     The function to map over the items (typically funcs).
/// </param>
/// <param name="_arg1">
///     The multiset of <c>Guarded</c>s over which we are mapping.
/// </param>
/// <returns>
///     The multiset <c>Guarded</c>s resulting from the map.
/// </returns>
let mapItems f = Multiset.map (mapItem f)

/// <summary>
///     Removes false guards from a guarded multiset.
/// </summary>
/// <param name="gset">
///     The multiset of <c>Guarded</c>s to prune.
/// </param>
/// <returns>
///     The multiset of <c>Guarded</c>s after removing items with guards
///     that are always false.
/// </returns>
let pruneGuardedSet gset =
    gset
    |> Multiset.toFlatSeq
    |> Seq.filter (function
                   | Never _ -> false
                   | _       -> true)
    |> Multiset.ofFlatSeq


/// <summary>
///     Pretty printers for guarded items.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Model.Pretty

    /// <summary>
    ///     Pretty-prints a guarded item.
    ///
    ///     <para>
    ///         Always-true guards are omitted.
    ///         Always-false guards cause the item to be surrounded by
    ///         tildes (in shameless imitation of GitHub Flavoured Markdown).
    ///         Other guards are placed before their guarded items with an
    ///         arrow to separate them.
    ///     </para>
    /// </summary>
    /// <param name="pitem">
    ///     A pretty-printer for the <c>Item</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The guard to pretty-print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the guarded item.
    /// </returns>
    let printGuarded pitem =
        function
        | Always i -> pitem i
        | Never i -> ssurround "~" "~" (pitem i)
        | { Cond = c ; Item = i } ->
            parened (HSep([ printBoolExpr c
                            pitem i ], String " -> "))

    /// <summary>
    ///     Pretty-prints a guarded <c>VFunc</c>.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>GFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>GFunc</c>.
    /// </returns>
    let printGFunc = printGuarded printVFunc

    /// <summary>
    ///     Pretty-prints a guarded view.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>GView</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>GView</c>.
    /// </returns>
    let printGView = printMultiset printGFunc >> ssurround "<|" "|>"

    /// <summary>
    ///     Pretty-prints a guarded view set.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>ViewSet</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>ViewSet</c>.
    /// </returns>
    let printViewSet =
        printMultiset (printGuarded printView >> ssurround "((" "))")
        >> ssurround "(|" "|)"
