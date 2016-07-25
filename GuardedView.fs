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
open Starling.Core.Sub
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Model.Sub


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
    type Guarded<'var, 'item> =
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
    type GFunc<'var> = Guarded<'var, VFunc<'var>>

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

    /// <summary>
    ///     A <c>GView</c> over <c>MarkedVar</c>s.
    /// </summary>
    type MGView = GView<MarkedVar>

    /// <summary>
    ///     A <c>GView</c> over symbolic <c>Var</c>s.
    /// </summary>
    type SVGView = GView<Sym<Var>>

    /// <summary>
    ///     A <c>GView</c> over symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMGView = GView<Sym<MarkedVar>>

    /// <summary>
    ///     A multiset of guarded views, as produced by reification.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the guard.
    /// </typeparam>
    type ViewSet<'var> when 'var : comparison =
        Multiset<Guarded<'var, OView>>

    /// <summary>
    ///     A <c>ViewSet</c> over <c>MarkedVar</c>s.
    /// </summary>
    type MViewSet = ViewSet<MarkedVar>

    /// <summary>
    ///     A <c>ViewSet</c> over symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMViewSet = ViewSet<Sym<MarkedVar>>


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
    open Starling.Core.Var.Pretty
    open Starling.Core.Symbolic.Pretty
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
    let printGuarded pVar pItem =
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
    let printMGuarded pItem = printGuarded printMarkedVar pItem

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
    let printGFunc pVar = printGuarded pVar (printVFunc pVar)

    /// <summary>
    ///     Pretty-prints a guarded <c>VFunc</c> over <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>MGFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>MGFunc</c>.
    /// </returns>
    let printMGFunc = printGFunc printMarkedVar

    /// <summary>
    ///     Pretty-prints a <c>GFunc</c> over symbolic <c>Var</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SGFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SGFunc</c>.
    /// </returns>
    let printSVGFunc = printGFunc (printSym String)

    /// <summary>
    ///     Pretty-prints a guarded <c>VFunc</c> over symbolic <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SMGFunc</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SMGFunc</c>.
    /// </returns>
    let printSMGFunc = printGFunc (printSym printMarkedVar)

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
    let printGView pVar =
        printMultiset (printGFunc pVar)
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
    let printMGView = printGView printMarkedVar

    /// <summary>
    ///     Pretty-prints a guarded view over symbolic <c>Var</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SGView</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SGView</c>.
    /// </returns>
    let printSVGView : SVGView -> Doc = printGView (printSym String)

    /// <summary>
    ///     Pretty-prints a guarded view over symbolic <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SMGView</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SMGView</c>.
    /// </returns>
    let printSMGView = printGView (printSym printMarkedVar)

    /// <summary>
    ///     Pretty-prints a guarded view set.
    /// </summary>
    /// <param name="pVar">
    ///     A pretty-printer for variables in the <c>Cond</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>ViewSet</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>ViewSet</c>.
    /// </returns>
    let printViewSet pVar =
        printMultiset (printGuarded pVar printOView >> ssurround "((" "))")
        >> ssurround "(|" "|)"

    /// <summary>
    ///     Pretty-prints a guarded view set over <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>MViewSet</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>MViewSet</c>.
    /// </returns>
    let printMViewSet =
        printViewSet printMarkedVar

    /// <summary>
    ///     Pretty-prints a guarded view set over symbolic <c>MarkedVar</c>s.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>SMViewSet</c> to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command to print the <c>SMViewSet</c>.
    /// </returns>
    let printSMViewSet = printViewSet (printSym printMarkedVar)

/// <summary>
///     Functions for substituting over guarded views.
/// </summary>
module Sub =
    open Starling.Core.Sub

    /// <summary>
    ///   Maps a <c>SubFun</c> over all expressions in a <c>GFunc</c>.
    /// </summary>
    /// <param name="sub">
    ///     The <c>SubFun</c> to map.
    /// </param>
    /// <param name="context">
    ///     The context to pass to the <c>SubFun</c>.
    /// </param>
    /// <param name="_arg1">
    ///   The <c>GFunc</c> over which whose expressions are to be mapped.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <returns>
    ///   The <c>GFunc</c> resulting from the mapping.
    /// </returns>
    /// <remarks>
    ///   <para>
    ///     The expressions in a <c>GFunc</c> are the guard itself, and
    ///     the expressions of the enclosed <c>VFunc</c>.
    ///   </para>
    /// </remarks>
    let subExprInGFunc
      (sub : SubFun<'srcVar, 'dstVar>)
      (context : SubCtx)
      ( { Cond = cond ; Item = item } : GFunc<'srcVar> )
      : (SubCtx * GFunc<'dstVar>) =
        let contextC, cond' =
            Position.changePos
                Position.negate
                (Mapper.mapBoolCtx sub)
                context
                cond
        let context', item' =
            Position.changePos
                id
                (subExprInVFunc sub)
                context
                item

        (context', { Cond = cond'; Item = item' } )

    /// <summary>
    ///   Maps a <c>SubFun</c> over all expressions in a <c>GView</c>.
    /// </summary>
    /// <param name="sub">
    ///   The <c>SubFun</c> to map over all expressions in the <c>GView</c>.
    /// </param>
    /// <param name="context">
    ///     The context to pass to the <c>SubFun</c>.
    /// </param>
    /// <param name="_arg1">
    ///   The <c>GView</c> over which whose expressions are to be mapped.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <returns>
    ///   The <c>GView</c> resulting from the mapping.
    /// </returns>
    /// <remarks>
    ///   <para>
    ///     The expressions in a <c>GView</c> are those of its constituent
    ///     <c>GFunc</c>s.
    ///   </para>
    /// </remarks>
    let subExprInGView
      (sub : SubFun<'srcVar, 'dstVar>)
      (context : SubCtx)
      : GView<'srcVar> -> (SubCtx * GView<'dstVar>) =
        Multiset.mapAccum
            (fun ctx f _ ->
                 Position.changePos
                     id
                     (subExprInGFunc sub)
                     ctx
                     f)
            context

    /// <summary>
    ///     Maps a <c>SubFun</c> over all expressions in an <c>Term</c>
    ///     over a <c>GView</c> weakest-pre and <c>VFunc</c> goal.
    /// </summary>
    /// <param name="sub">
    ///     The <c>SubFun</c> to map over all expressions in the <c>STerm</c>.
    /// </param>
    /// <param name="context">
    ///     The context to pass to the <c>SubFun</c>.
    /// </param>
    /// <param name="term">
    ///     The <c>Term</c> over which expressions are to be mapped.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <returns>
    ///     The <c>Term</c> resulting from the mapping.
    /// </returns>
    /// <remarks>
    ///     <para>
    ///         The expressions in the term are those of its
    ///         constituent command (<c>BoolExpr</c>), its weakest
    ///         precondition (<c>GView</c>), and its goal (<c>VFunc</c>).
    ///     </para>
    /// </remarks>
    let subExprInDTerm
      (sub : SubFun<'srcVar, 'dstVar>)
      (context : SubCtx)
      (term : Term<BoolExpr<'srcVar>, GView<'srcVar>, VFunc<'srcVar>>)
      : (SubCtx * Term<BoolExpr<'dstVar>, GView<'dstVar>, VFunc<'dstVar>>) =
        let contextT, cmd' =
            Position.changePos
                Position.negate
                (Mapper.mapBoolCtx sub)
                context
                term.Cmd
        let contextW, wpre' =
            Position.changePos
                Position.negate
                (subExprInGView sub)
                contextT
                term.WPre
        let context', goal' =
            Position.changePos
                id
                (subExprInVFunc sub)
                contextW
                term.Goal
        (context', { Cmd = cmd'; WPre = wpre'; Goal = goal' } )

    /// <summary>
    ///     Maps a <c>TrySubFun</c> over all expressions in a <c>GFunc</c>.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>GFunc</c> over which whose expressions are to be mapped.
    /// </param>
    /// <param name="context">
    ///     The context to pass to the <c>SubFun</c>.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of errors occurring in the map.
    /// </typeparam>
    /// <returns>
    ///     The Chessie-wrapped <c>GFunc</c> resulting from the mapping.
    /// </returns>
    /// <remarks>
    ///     <para>
    ///         The expressions in a <c>GFunc</c> are the guard itself, and
    ///         the expressions of the enclosed <c>VFunc</c>.
    ///     </para>
    /// </remarks>
    let trySubExprInGFunc
      (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
      (context : SubCtx)
      ( { Cond = cond ; Item = item } : GFunc<'srcVar> )
      : (SubCtx * Result<GFunc<'dstVar>, 'err> ) =
        let contextC, cond' =
            Position.changePos
                Position.negate
                (Mapper.mapBoolCtx sub)
                context
                cond
        let context', item' =
            Position.changePos
                id
                (trySubExprInVFunc sub)
                context
                item

        (context',
         lift2
             (fun cond' item' -> { Cond = cond' ; Item = item' } )
             cond'
             item')

    /// <summary>
    ///     Maps a <c>TrySubFun</c> over all expressions in a <c>GView</c>.
    /// </summary>
    /// <param name="sub">
    ///     The <c>TrySubFun</c> to map over all expressions in the
    ///     <c>GView</c>.
    /// </param>
    /// <param name="context">
    ///     The context to pass to the <c>SubFun</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>GView</c> over which whose expressions are to be mapped.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <returns>
    ///     The Chessie-wrapped <c>GView</c> resulting from the mapping.
    /// </returns>
    /// <remarks>
    ///     <para>
    ///         The expressions in a <c>GView</c> are those of its
    ///         constituent <c>GFunc</c>s.
    ///     </para>
    /// </remarks>
    let trySubExprInGView
      (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
      (context : SubCtx)
      : GView<'srcVar> -> (SubCtx * Result<GView<'dstVar>, 'err> ) =
        Multiset.mapAccum
            (fun ctx f _ ->
                 Position.changePos
                     id
                     (trySubExprInGFunc sub)
                     ctx f)
            context
        >> pairMap id Multiset.collect

    /// <summary>
    ///     Maps a <c>TrySubFun</c> over all expressions in a <c>Term</c>
    ///     over a <c>GView</c> weakest-pre and <c>VFunc</c> goal.
    /// </summary>
    /// <param name="sub">
    ///     The <c>TrySubFun</c> to map over all expressions in the
    ///     <c>Term</c>.
    /// </param>
    /// <param name="context">
    ///     The context to pass to the <c>SubFun</c>.
    /// </param>
    /// <param name="term">
    ///     The <c>Term</c> over which expressions are to be mapped.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <returns>
    ///     The Chessie-wrapped <c>Term</c> resulting from the mapping.
    /// </returns>
    /// <remarks>
    ///     <para>
    ///         The expressions in the term are those of its
    ///         constituent command (<c>BoolExpr</c>), its weakest
    ///         precondition (<c>GView</c>), and its goal (<c>VFunc</c>).
    ///     </para>
    /// </remarks>
    let trySubExprInDTerm
      (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
      (context : SubCtx)
      (term : Term<BoolExpr<'srcVar>, GView<'srcVar>, VFunc<'srcVar>>)
      : (SubCtx * Result<Term<BoolExpr<'dstVar>, GView<'dstVar>, VFunc<'dstVar>>, 'err> ) =
        let contextT, cmd' =
            Position.changePos
                Position.negate
                (Mapper.mapBoolCtx sub)
                context
                term.Cmd
        let contextW, wpre' =
            Position.changePos
                Position.negate
                (trySubExprInGView sub)
                contextT
                term.WPre
        let context', goal' =
            Position.changePos
                id
                (trySubExprInVFunc sub)
                contextW
                term.Goal
        (context',
         lift3
             (fun c w g -> { Cmd = c; WPre = w; Goal = g } )
             cmd'
             wpre'
             goal')


/// <summary>
///     Tests for guarded views.
/// </summary>
module Tests =
    open NUnit.Framework

    open Starling.Utils.Testing
    open Starling.Core.TypeSystem

    /// <summary>
    ///     Test substitution function for position-based substitution.
    /// </summary>
    let positionTestSub =
        (onVars
             (Mapper.makeCtx
                  (fun ctx _ ->
                       (ctx,
                        match ctx with
                        | Positions (Positive::xs) -> AInt 1L
                        | Positions (Negative::xs) -> AInt 0L
                        | _ -> AInt -1L ))
                  (fun ctx _ ->
                       (ctx,
                        match ctx with
                        | Positions (x::xs) -> Position.overapprox x
                        | _ -> BVar "?"))))

    /// <summary>
    ///     NUnit tests for guarded views.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Case studies for <c>testPositionSubExprInGFunc</c>.
        /// </summary>
        static member PositionSubExprInGFuncCases =
            [ (tcd
                   [| gfunc (BVar "foo") "bar"
                          [ Typed.Int (AVar "baz")
                            Typed.Bool (BVar "fizz") ]
                      Position.positive |] )
                  .Returns(
                      (Position.positive,
                       (gfunc BFalse "bar"
                            [ Typed.Int (AInt 1L)
                              Typed.Bool BTrue ] : GFunc<Var> )))
                  .SetName("GFunc substitution in +ve case works properly")
              (tcd
                   [| gfunc (BVar "foo") "bar"
                          [ Typed.Int (AVar "baz")
                            Typed.Bool (BVar "fizz") ]
                      Position.negative |] )
                  .Returns(
                      (Position.negative,
                       (gfunc BTrue "bar"
                            [ Typed.Int (AInt 0L)
                              Typed.Bool BFalse ] : GFunc<Var> )))
                  .SetName("GFunc substitution in -ve case works properly") ]

        /// <summary>
        ///     Tests <c>subExprInGFunc</c> on positional substitutions.
        /// </summary>
        [<TestCaseSource("PositionSubExprInGFuncCases")>]
        member this.testPositionSubExprInGFunc
          (gf : GFunc<Var>)
          (pos : SubCtx) =
            Sub.subExprInGFunc
                positionTestSub
                pos
                gf

        /// <summary>
        ///     Case studies for <c>testPositionSubExprInGView</c>.
        /// </summary>
        static member PositionSubExprInGViewCases =
            [ (tcd
                   [| (Multiset.empty : GView<Var>)
                      Position.positive |] )
                  .Returns(
                      (Position.positive,
                       (Multiset.empty : GView<Var>)))
                  .SetName("+ve empty GView substitution is a no-op")
              (tcd
                   [| (Multiset.empty : GView<Var>)
                      Position.negative |] )
                  .Returns(
                      (Position.negative,
                       (Multiset.empty : GView<Var>)))
                  .SetName("-ve empty GView substitution is a no-op")
              (tcd
                   [| Multiset.singleton
                          (gfunc (BVar "foo") "bar"
                               [ Typed.Int (AVar "baz")
                                 Typed.Bool (BVar "fizz") ] )
                      Position.positive |] )
                  .Returns(
                      (Position.positive,
                       (Multiset.singleton
                            (gfunc BFalse "bar"
                                 [ Typed.Int (AInt 1L)
                                   Typed.Bool BTrue ] ) : GView<Var> )))
                  .SetName("Singleton GView substitution in +ve case works properly")
              (tcd
                   [| Multiset.singleton
                          (gfunc (BVar "foo") "bar"
                               [ Typed.Int (AVar "baz")
                                 Typed.Bool (BVar "fizz") ] )
                      Position.negative |] )
                  .Returns(
                      (Position.negative,
                       (Multiset.singleton
                            (gfunc BTrue "bar"
                                 [ Typed.Int (AInt 0L)
                                   Typed.Bool BFalse ] ) : GView<Var> )))
                  .SetName("Singleton GView substitution in -ve case works properly")
              (tcd
                   [| Multiset.ofFlatList
                          [ gfunc (BVar "foo") "bar"
                                [ Typed.Int (AVar "baz")
                                  Typed.Bool (BVar "fizz") ]
                            gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                [ Typed.Int
                                      (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                      Position.positive |] )
                  .Returns(
                      (Position.positive,
                       (Multiset.ofFlatList
                            [ gfunc BFalse "bar"
                                  [ Typed.Int (AInt 1L)
                                    Typed.Bool BTrue ]
                              gfunc (BGt (AInt 0L, AInt 0L)) "barbaz"
                                  [ Typed.Int
                                        (AAdd [ AInt 1L; AInt 1L ]) ] ]
                        : GView<Var>)))
                  .SetName("Multi GView substitution in +ve case works properly")
              (tcd
                   [| Multiset.ofFlatList
                          [ gfunc (BVar "foo") "bar"
                                [ Typed.Int (AVar "baz")
                                  Typed.Bool (BVar "fizz") ]
                            gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                [ Typed.Int
                                      (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                      Position.negative |] )
                  .Returns(
                      (Position.negative,
                       (Multiset.ofFlatList
                            [ gfunc BTrue "bar"
                                  [ Typed.Int (AInt 0L)
                                    Typed.Bool BFalse ]
                              gfunc (BGt (AInt 1L, AInt 1L)) "barbaz"
                                  [ Typed.Int
                                        (AAdd [ AInt 0L; AInt 0L ]) ] ]
                        : GView<Var>)))
                  .SetName("Multi GView substitution in -ve case works properly") ]

        /// <summary>
        ///     Tests <c>subExprInGView</c> on positional substitutions.
        /// </summary>
        [<TestCaseSource("PositionSubExprInGViewCases")>]
        member this.testPositionSubExprInGView
          (gv : GView<Var>)
          (pos : SubCtx) =
            Sub.subExprInGView
                positionTestSub
                pos
                gv

        /// <summary>
        ///     Case studies for <c>testPositionSubExprInDTerm</c>.
        /// </summary>
        static member PositionSubExprInDTermCases =
            [ (tcd
                   [| ( { Cmd =
                              BAnd
                                  [ bEq (BVar "foo") (BVar "bar")
                                    bEq (BVar "baz") (BNot (BVar "baz")) ]
                          WPre =
                              Multiset.ofFlatList
                                  [ gfunc (BVar "foo") "bar"
                                        [ Typed.Int (AVar "baz")
                                          Typed.Bool (BVar "fizz") ]
                                    gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                        [ Typed.Int
                                              (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                          Goal =
                              (vfunc "bar"
                                   [ Typed.Int (AVar "baz")
                                     Typed.Bool (BVar "barbaz") ] : VFunc<Var> ) }
                       : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )
                      Position.positive |] )
                  .Returns(
                      (Position.positive,
                       ( { Cmd =
                               BAnd
                                   [ bEq BFalse BFalse
                                     bEq BFalse (BNot BTrue) ]
                           WPre =
                               Multiset.ofFlatList
                                   [ gfunc BTrue "bar"
                                         [ Typed.Int (AInt 0L)
                                           Typed.Bool BFalse ]
                                     gfunc (BGt (AInt 1L, AInt 1L)) "barbaz"
                                         [ Typed.Int
                                               (AAdd [ AInt 0L; AInt 0L ]) ] ]
                           Goal =
                               (vfunc "bar"
                                    [ Typed.Int (AInt 1L)
                                      Typed.Bool BTrue ] : VFunc<Var> ) }
                        : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )))
                  .SetName("Successfully translate a positive DTerm")
              (tcd
                   [| ( { Cmd =
                              BAnd
                                  [ bEq (BVar "foo") (BVar "bar")
                                    bEq (BVar "baz") (BNot (BVar "baz")) ]
                          WPre =
                              Multiset.ofFlatList
                                  [ gfunc (BVar "foo") "bar"
                                        [ Typed.Int (AVar "baz")
                                          Typed.Bool (BVar "fizz") ]
                                    gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                        [ Typed.Int
                                              (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                          Goal =
                              (vfunc "bar"
                                   [ Typed.Int (AVar "baz")
                                     Typed.Bool (BVar "barbaz") ] : VFunc<Var> ) }
                       : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )
                      Position.negative |] )
                  .Returns(
                      (Position.negative,
                       ( { Cmd =
                               BAnd
                                   [ bEq BTrue BTrue
                                     bEq BTrue (BNot BFalse) ]
                           WPre =
                               Multiset.ofFlatList
                                   [ gfunc BFalse "bar"
                                         [ Typed.Int (AInt 1L)
                                           Typed.Bool BTrue ]
                                     gfunc (BGt (AInt 0L, AInt 0L)) "barbaz"
                                         [ Typed.Int
                                               (AAdd [ AInt 1L; AInt 1L ]) ] ]
                           Goal =
                               (vfunc "bar"
                                    [ Typed.Int (AInt 0L)
                                      Typed.Bool BFalse ] : VFunc<Var> ) }
                        : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )))
                  .SetName("Successfully translate a negative DTerm") ]

        /// <summary>
        ///     Tests <c>subExprInDTerm</c> on positional substitutions.
        /// </summary>
        [<TestCaseSource("PositionSubExprInDTermCases")>]
        member this.testPositionSubExprInDTerm
          (t : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>>)
          (pos : SubCtx) =
            Sub.subExprInDTerm
                positionTestSub
                pos
                t
