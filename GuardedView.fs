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

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Traversal
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.Symbolic
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
    /// <typeparam name="var">
    ///     The type of variables in the guard.
    /// </typeparam>
    /// <typeparam name="item">
    ///     The type of the guarded item.
    /// </typeparam>
    type Guarded<'var, 'item> when 'var : equality =
        { /// <summary>
          ///    The guard condition.
          /// </summary>
          Cond : BoolExpr<'var>
          /// <summary>
          ///    The guarded item.
          /// </summary>
          Item : 'item }
        override this.ToString() = sprintf "(%A -> %A)" this.Cond this.Item

    (*
     * Shorthand for guarded items.
     *)

    /// <summary>
    ///     A guarded <c>VFunc</c>.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the guard.
    /// </typeparam>
    type GFunc<'var> when 'var : equality = Guarded<'var, VFunc<'var>>

    /// <summary>
    ///     A guarded iterated <c>VFunc</c>.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the guard.
    /// </typeparam>
    type IteratedGFunc<'Var> when 'Var : equality =
        IteratedContainer<GFunc<'Var>, IntExpr<'Var>>

    /// <summary>
    ///     A <c>GFunc</c> over <c>MarkedVar</c>s.
    /// </summary>
    type MGFunc = GFunc<MarkedVar>

    /// <summary>
    ///     A <c>GFunc</c> over symbolic <c>Var</c>s.
    /// </summary>
    type SVGFunc = GFunc<Sym<Var>>

    /// <summary>
    ///     A <c>GFunc</c> over symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMGFunc = GFunc<Sym<MarkedVar>>

    /// <summary>
    ///     A guarded view.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the guard.
    /// </typeparam>
    /// <remarks>
    ///     These are the most common form of view in Starling internally,
    ///     although theoretically speaking they are equivalent to Views
    ///     with the guards lifting to proof case splits.
    /// </remarks>
    type GView<'var> when 'var : comparison =
        Multiset<GFunc<'var>>

    /// An iterated GView
    /// i.e. a GView but containing Iterated forms of the GFunc's
    type IteratedGView<'var> when 'var : comparison =
        Multiset<IteratedGFunc<'var>>

    /// <summary>
    ///     A view produced by expanding a sub-view of an guarded view.
    ///     <para>
    ///         The entire view (not its individual funcs) is guarded, by the
    ///         conjunction of the guards over the sub-view's original guarded
    ///         funcs.
    ///     </para>
    /// </summary>
    type GuardedIteratedSubview = Guarded<Sym<MarkedVar>, IteratedOView>

    /// <summary>
    ///     A view produced by iter-lowering a
    ///     <see cref="GuardedIteratedSubView"/>.
    ///     <para>
    ///         The entire view (not its individual funcs) is guarded, by the
    ///         conjunction of the guards over the sub-view's original guarded
    ///         funcs.
    ///     </para>
    /// </summary>
    type GuardedSubview = Guarded<Sym<MarkedVar>, OView>

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
/// <typeparam name="var">
///     The type of variables in the <c>GFunc</c>'s parameters.
/// </typeparam>
/// <returns>
///     A new <c>GFunc</c> with the given guard, name, and parameters.
/// </returns>
let gfunc
  (guard : BoolExpr<'var>)
  (name : string)
  (pars : Expr<'var> seq)
  : GFunc<'var> =
    { Cond = guard ; Item = vfunc name pars }

/// <summary>
///     Creates a new <c>SVGFunc</c>.
/// </summary>
/// <param name="guard">
///     The guard on which the <c>SVGFunc</c> is conditional.
/// </param>
/// <param name="name">
///     The name of the <c>SVGFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>SVGFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>SVGFunc</c> with the given guard, name, and parameters.
/// </returns>
let svgfunc (guard : SVBoolExpr) (name : string) (pars : SVExpr seq) : SVGFunc =
    gfunc guard name pars

/// <summary>
///     Creates a new <c>MGFunc</c>.
/// </summary>
/// <param name="guard">
///     The guard on which the <c>MGFunc</c> is conditional.
/// </param>
/// <param name="name">
///     The name of the <c>MGFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>MGFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>MGFunc</c> with the given guard, name, and parameters.
/// </returns>
let mgfunc (guard : MBoolExpr) (name : string) (pars : MExpr seq) : MGFunc =
    gfunc guard name pars

/// <summary>
///     Creates a new <c>SMGFunc</c>.
/// </summary>
/// <param name="guard">
///     The guard on which the <c>SMGFunc</c> is conditional.
/// </param>
/// <param name="name">
///     The name of the <c>SMGFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>SMGFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>SMGFunc</c> with the given guard, name, and parameters.
/// </returns>
let smgfunc (guard : SMBoolExpr) (name : string) (pars : SMExpr seq) : SMGFunc =
    gfunc guard name pars

/// <summary>
///     Constructs an iterated guarded func.
/// </summary>
/// <param name="guard">The guard on which the func is conditional.</param>
/// <param name="name">The name of the func.</param>
/// <param name="pars">The parameters of the func, as a sequence.</param>
/// <param name="iter">The iterator.</param>
/// <typeparam name="Var">The type of expression variables.</typeparam>
/// <returns>
///     The <see cref="IteratedGFunc"/> iterating over the func with name
///     <paramref name="name"/> and params <paramref name="pars"/>
///     <paramref name="it"/> times, subject to <paramref name="guard"/>
///     holding.
/// </returns>
let iteratedGFunc (guard : BoolExpr<'Var>) (name : string)
  (pars : Expr<'Var> seq) (iter : IntExpr<'Var>)
  : IteratedGFunc<'Var> =
    iterated (gfunc guard name pars) iter

(*
 * Single-guard active patterns.
 *)

/// <summary>
///     Active pattern matching on trivially true guards.
/// </summary>
let (|Always|_|)
  ({ Cond = c ; Item = i } : Guarded<'var, 'item>)
  : 'item option =
    if isTrue c then Some i else None

/// <summary>
///     Active pattern matching on trivially false guards.
/// </summary>
let (|Never|_|)
  ({ Cond = c ; Item = i } : Guarded<'var, 'item>)
  : 'item option =
    if isFalse c then Some i else None


(*
 * Destructuring and mapping.
 *)

/// <summary>
///     Converts a <c>Guarded</c> to a tuple.
/// </summary>
/// <param name="_arg1">
///     The <c>Guarded</c> to destructure.
/// </param>
/// <returns>
///     The tuple <c>(c, i)</c>, where <c>c</c> is the guard condition
///     of <paramref name="_arg1" />, and <c>i</c> its item.
/// </returns>
let gFuncTuple
  ({ Cond = c ; Item = i } : Guarded<'var, 'item>)
  : BoolExpr<'var> * 'item = (c, i)


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
let mapCond
  (f : BoolExpr<'varA> -> BoolExpr<'varB>)
  ({ Cond = c ; Item = i } : Guarded<'varA, _>)
  : Guarded<'varB, _ > = { Cond = f c ; Item = i }

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
let mapItem
  (f : 'itemA -> 'itemB)
  ({ Cond = c ; Item = i } : Guarded<_, 'itemA>)
  : Guarded<_, 'itemB> = { Cond = c ; Item = f i }

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
let mapConds
  (f : BoolExpr<'itemA> -> BoolExpr<'itemB>)
  : Multiset<Guarded<'itemA, _>> -> Multiset<Guarded<'itemB, _>> =
    Multiset.map (mapCond f)

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
let mapItems
  (f : 'itemA -> 'itemB)
  : Multiset<Guarded<_, 'itemA>> -> Multiset<Guarded<_, 'itemB>> =
    Multiset.map (mapItem f)

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
let pruneGuardedSet (gset : Multiset<Guarded<_, _>>)
  : Multiset<Guarded<_, _>> =
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
    open Starling.Collections.Multiset.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.View.Pretty

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
    /// <param name="pVar">
    ///     A pretty-printer for variables in the <c>Cond</c>.
    /// </param>
    /// <param name="pItem">
    ///     A pretty-printer for the <c>Item</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The guard to pretty-print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the guarded item.
    /// </returns>
    let printGuarded (pVar : 'var -> Doc) (pItem : 'item -> Doc)
      : Guarded<'var, 'item> -> Doc =
        function
        | Always i -> pItem i
        | Never i -> ssurround "~" "~" (pItem i)
        | { Cond = c ; Item = i } ->
            parened (HSep([ printBoolExpr pVar c
                            pItem i ], String " -> "))

    /// <summary>
    ///     Pretty-prints a guarded item over <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="pItem">
    ///     A pretty-printer for the <c>Item</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The guard to pretty-print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the guarded item.
    /// </returns>
    let printMGuarded
      (pItem : 'item -> Doc)
      : Guarded<MarkedVar, 'item> -> Doc = printGuarded printMarkedVar pItem

    /// <summary>
    ///     Pretty-prints a guarded <c>VFunc</c>.
    /// </summary>
    /// <param name="pVar">
    ///     A pretty-printer for variables in the <c>Cond</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>GFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>GFunc</c>.
    /// </returns>
    let printGFunc (pVar : 'var -> Doc) : GFunc<'var> -> Doc =
        printGuarded pVar (printVFunc pVar)

    /// <summary>
    ///     Pretty-prints a guarded <c>VFunc</c> over <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>MGFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>MGFunc</c>.
    /// </returns>
    let printMGFunc : GFunc<MarkedVar> -> Doc = printGFunc printMarkedVar

    /// <summary>
    ///     Pretty-prints a <c>GFunc</c> over symbolic <c>Var</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SGFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SGFunc</c>.
    /// </returns>
    let printSVGFunc : GFunc<Sym<Var>> -> Doc = printGFunc (printSym String)

    /// <summary>
    ///     Pretty-prints a guarded <c>VFunc</c> over symbolic <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SMGFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SMGFunc</c>.
    /// </returns>
    let printSMGFunc : GFunc<Sym<MarkedVar>> -> Doc =
        printGFunc (printSym printMarkedVar)

    /// <summary>
    ///     Pretty-prints a guarded view.
    /// </summary>
    /// <param name="pVar">
    ///     A pretty-printer for variables in the <c>Cond</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>GView</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>GView</c>.
    /// </returns>
    let printGView (pVar : 'var -> Doc) : GView<'var> -> Doc =
        printMultiset (printGFunc pVar)
        >> ssurround "<|" "|>"

    let printIteratedGView (pVar : 'var -> Doc) : IteratedGView<'var> -> Doc =
        printMultiset
            (printIteratedContainer (printGFunc pVar) (printIntExpr pVar))
        >> ssurround "<|" "|>"

    /// <summary>
    ///     Pretty-prints a guarded view over <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>MGView</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>MGView</c>.
    /// </returns>
    let printMGView : GView<MarkedVar> -> Doc = printGView printMarkedVar

    /// <summary>
    ///     Pretty-prints a guarded view over symbolic <c>Var</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The view to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the view.
    /// </returns>
    let printSVGView : GView<Sym<Var>> -> Doc = printGView (printSym String)

    /// <summary>
    ///     Pretty-prints an iterated guarded view over symbolic <c>Var</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The view to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the view.
    /// </returns>
    let printIteratedSVGView : IteratedGView<Sym<Var>> -> Doc = printIteratedGView (printSym String)

    /// <summary>
    ///     Pretty-prints a guarded view over symbolic <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The view to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the view.
    /// </returns>
    let printSMGView : GView<Sym<MarkedVar>> -> Doc =
        printGView (printSym printMarkedVar)

    /// <summary>
    ///     Pretty-prints a set of subviews.
    /// </summary>
    /// <param name="pSubview">
    ///     A pretty-printer for the subview.
    /// </param>
    /// <typeparam name="Subview">
    ///     The type of subviews in the set.
    /// </typeparam>
    /// <returns>
    ///     A function printing subview sets.
    /// </returns>
    let printSubviewSet (pSubview : 'Subview -> Doc) : Set<'Subview> -> Doc =
        Set.toSeq
        >> Seq.map (pSubview >> ssurround "((" "))")
        >> commaSep
        >> ssurround "[" "]"

    /// <summary>
    ///     Pretty-prints a guarded iterated subview over symbolic
    ///     <c>MarkedVar</c>s.
    /// </summary>
    let printGuardedIteratedSubview : GuardedIteratedSubview -> Doc =
        printGuarded (printSym printMarkedVar) printIteratedOView

    /// <summary>
    ///     Pretty-prints a guarded subview over symbolic <c>MarkedVar</c>s.
    /// </summary>
    let printGuardedSubview : GuardedSubview -> Doc =
        printGuarded (printSym printMarkedVar) printOView

/// <summary>
///     Functions for traversing guarded views.
/// </summary>
module Traversal =
    open Starling.Core.Traversal
    open Starling.Core.View
    open Starling.Core.View.Traversal
    open Starling.Core.Command.Traversal

    /// <summary>
    ///     Lifts a <c>Traversal</c> over all expressions in a guarded func.
    /// </summary>
    /// <param name="traversal">
    ///     The <c>Traversal</c> to map over all expressions in the guarded
    ///     func.  This should map from expressions to expressions.
    /// </param>
    /// <typeparam name="SrcVar">
    ///     The type of variables before traversal.
    /// </typeparam>
    /// <typeparam name="DstVar">
    ///     The type of variables after traversal.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverGFunc
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
      : Traversal<GFunc<'SrcVar>, GFunc<'DstVar>, 'Error, 'Var> =
        fun ctx { Cond = cond; Item = item } ->
            let tBool = traverseBoolAsExpr traversal
            let tFunc = tliftOverFunc traversal
            (* Remember: the condition of a guarded func is in a negative
               position! *)
            tchain2 (changePos negate tBool) tFunc
                (fun (cond', item') -> { Cond = cond'; Item = item' })
                ctx
                // Internal value, so it doesn't have an extended type
                (normalBool cond, item)

    /// <summary>
    ///     Lifts a <c>Traversal</c> over all expressions in an iterated
    ///     guarded func.
    /// </summary>
    /// <param name="traversal">
    ///     The <c>Traversal</c> to map over all expressions in the guarded
    ///     func.  This should map from expressions to expressions.
    /// </param>
    /// <typeparam name="SrcVar">
    ///     The type of variables before traversal.
    /// </typeparam>
    /// <typeparam name="DstVar">
    ///     The type of variables after traversal.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverIteratedGFunc
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
      : Traversal<IteratedGFunc<'SrcVar>, IteratedGFunc<'DstVar>, 'Error, 'Var> =
        fun ctx { Iterator = iter ; Func = func } ->
            let tInt = traverseIntAsExpr traversal
            let tGFunc = tliftOverGFunc traversal
            tchain2 tInt tGFunc
                (fun (iter', func') -> { Iterator = iter'; Func = func' })
                ctx
                // Internal value, so it doesn't have an extended type
                (normalInt iter, func)

    /// <summary>
    ///     Lifts a <c>Traversal</c> over all variables in a <see cref="Term"/>.
    /// </summary>
    /// <param name="traversal">
    ///     The <c>Traversal</c> to map over all variables in the term.
    ///     This should map from typed variables to expressions.
    /// </param>
    /// <typeparam name="SrcVar">
    ///     The type of variables before traversal.
    /// </typeparam>
    /// <typeparam name="DstVar">
    ///     The type of variables after traversal.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverTerm
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
      : Traversal<Term<BoolExpr<'SrcVar>, GView<'SrcVar>, VFunc<'SrcVar>>,
                  Term<BoolExpr<'DstVar>, GView<'DstVar>, VFunc<'DstVar>>,
                  'Error, 'Var> =
        fun ctx { Cmd = c ; WPre = w; Goal = g } ->
            let tCmd = traverseBoolAsExpr traversal
            let tWPre = tchainM (tliftOverGFunc traversal) id
            let tGoal = tliftOverFunc traversal

            (* Remember: Cmd and WPre are in a negative position, because
               the term is of the form Cmd /\ WPre => Goal. *)
            tchain3 (changePos negate tCmd) (changePos negate tWPre) tGoal
                (fun (c', w', g') -> { Cmd = c'; WPre = w'; Goal = g' })
                ctx
                // None of these items can have extended types, I think?
                (normalBool c, w, g)

    /// <summary>
    ///     Lifts a <c>Traversal</c> over all variables in a
    ///     <see cref="CmdTerm"/>.
    /// </summary>
    /// <param name="traversal">
    ///     The <c>Traversal</c> to map over all variables in the term.
    ///     This should map from typed variables to expressions.
    /// </param>
    /// <typeparam name="SrcVar">
    ///     The type of variables before traversal.
    /// </typeparam>
    /// <typeparam name="DstVar">
    ///     The type of variables after traversal.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverCmdTerm
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
      : Traversal<CmdTerm<BoolExpr<'SrcVar>, GView<'SrcVar>, VFunc<'SrcVar>>,
                  CmdTerm<BoolExpr<'DstVar>, GView<'DstVar>, VFunc<'DstVar>>,
                  'Error, 'Var> =
        fun ctx { Cmd = c ; WPre = w; Goal = g } ->
            let tCmd = tliftOverCommandSemantics traversal
            let tWPre = tchainM (tliftOverGFunc traversal) id
            let tGoal = tliftOverFunc traversal
            tchain3 tCmd tWPre tGoal
                (fun (c', w', g') -> { Cmd = c'; WPre = w'; Goal = g' })
                ctx
                (c, w, g)

/// Gets set of TypedVar's from a GFunc
let gFuncVars (gfunc : GFunc<Sym<Var>>)
  : Result<Set<TypedVar>, TraversalError<'Error>> =
    let tVars = tliftOverExpr collectSymVars
    findVars (Traversal.tliftOverGFunc tVars) gfunc

/// Gets set of TypedVars from an IteratedGFunc
let iteratedGFuncVars (itgfunc : IteratedGFunc<Sym<Var>>)
  : Result<Set<TypedVar>, TraversalError<'Error>> =
    let tVars = tliftOverExpr collectSymVars
    findVars (Traversal.tliftOverIteratedGFunc tVars) itgfunc
