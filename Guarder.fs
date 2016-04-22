module Starling.Lang.Guarder

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Lang.AST
open Starling.Lang.Modeller

/// Converts a func from conditional to guarded form.
/// This takes the set of all conditions forming the suffix of any guards
/// generated from this view.
let rec guardCFuncIn (suffix : Set<SVBoolExpr>) =
    function
    | CFunc.Func v ->
        [ { Cond =
                suffix
                |> Set.toList
                |> mkAnd
            Item = v } ]
    | CFunc.ITE(expr, tviews, fviews) ->
        List.concat [ guardCViewIn (suffix.Add expr) (Multiset.toFlatList tviews)
                      guardCViewIn (suffix.Add (mkNot expr)) (Multiset.toFlatList fviews) ]

/// Resolves a list of views, given a set of conditions held true.
and guardCViewIn suffix = concatMap (guardCFuncIn suffix)

/// Resolves a full condition-view multiset into a guarded-view multiset.
let guardCView : CView -> SVGView =
    // TODO(CaptainHayashi): woefully inefficient.
    Multiset.toFlatList
    >> guardCViewIn Set.empty
    >> Multiset.ofFlatList

/// Resolves a full condition-view ViewExpr into a guarded-view multiset.
let guardCViewExpr : ViewExpr<CView> -> ViewExpr<SVGView> =
    function
    | Mandatory v -> Mandatory (guardCView v)
    | Advisory v -> Advisory (guardCView v)

/// Converts a viewed command to guarded views.
let rec guardViewedCommand { Command = command ; Post = post } =
    { Command = guardPartCmd command ; Post = guardCViewExpr post }

/// Converts a block to guarded views.
and guardBlock {Pre = pre; Contents = contents} =
    { Pre = guardCViewExpr pre
      Contents = List.map guardViewedCommand contents }

/// Converts a PartCmd to guarded views.
and guardPartCmd : PartCmd<ViewExpr<CView>> -> PartCmd<ViewExpr<SVGView>> =
    function
    | Prim p -> Prim p
    | While (isDo, expr, inner) ->
        While (isDo, expr, guardBlock inner)
    | ITE (expr, inTrue, inFalse) ->
        ITE (expr, guardBlock inTrue, guardBlock inFalse)

/// Converts a method to guarded views.
let guardMethod { Signature = signature; Body = body } =
    { Signature = signature; Body = guardBlock body }

/// Converts an entire model to guarded views.
let guard : UVModel<PMethod<ViewExpr<CView>>>
         -> UVModel<PMethod<ViewExpr<SVGView>>> =
    mapAxioms guardMethod
