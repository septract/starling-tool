/// <summary>
///     The part of the language frontend that desugars conditional
///     (if-then-else) views to guarded views.
/// </summary>
module Starling.Lang.Guarder

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Lang.AST
open Starling.Lang.Modeller

[<AutoOpen>]
module Types =
    type GuarderViewExpr = ViewExpr<GView<Sym<Var>>>
    type GuarderPartCmd = PartCmd<GuarderViewExpr>
    type GuarderBlock = Block<GuarderViewExpr, GuarderPartCmd>
    type GuarderMethod = Method<GuarderViewExpr, GuarderPartCmd>

/// Resolves a full condition-view multiset into a guarded-view multiset.
let guardCView : CView -> GView<Sym<Var>> =
    let rec guardCFuncIn suffix =
        function
        | CFunc.Func v ->
            [ { Cond = suffix |> Set.toList |> mkAnd
                Item = v } ]
        | CFunc.ITE(expr, tviews, fviews) ->
            List.concat
                [ guardCViewIn (suffix.Add expr) (Multiset.toFlatList tviews)
                  guardCViewIn (suffix.Add (mkNot expr))
                      (Multiset.toFlatList fviews) ]
    and guardCViewIn suffix = concatMap (guardCFuncIn suffix)

    // TODO(CaptainHayashi): woefully inefficient.
    Multiset.toFlatList
    >> guardCViewIn Set.empty
    >> Multiset.ofFlatList

/// Resolves a full condition-view ViewExpr into a guarded-view multiset.
let guardCViewExpr : ModellerViewExpr -> GuarderViewExpr =
    function
    | Mandatory v -> Mandatory (guardCView v)
    | Advisory v -> Advisory (guardCView v)

/// Converts a viewed command to guarded views.
let rec guardViewedCommand
  ({ Command = command ; Post = post }
     : ViewedCommand<ModellerViewExpr, ModellerPartCmd>)
  : ViewedCommand<GuarderViewExpr, GuarderPartCmd> =
    { Command = guardPartCmd command ; Post = guardCViewExpr post }

/// Converts a block to guarded views.
and guardBlock
  ({Pre = pre; Contents = contents} : ModellerBlock)
  : GuarderBlock =
    { Pre = guardCViewExpr pre
      Contents = List.map guardViewedCommand contents }

/// Converts a PartCmd to guarded views.
and guardPartCmd : ModellerPartCmd -> GuarderPartCmd =
    function
    | Prim p -> Prim p
    | While (isDo, expr, inner) ->
        While (isDo, expr, guardBlock inner)
    | ITE (expr, inTrue, inFalse) ->
        ITE (expr, guardBlock inTrue, guardBlock inFalse)

/// Converts a method to guarded views.
let guardMethod
  ({ Signature = signature; Body = body } : ModellerMethod)
  : GuarderMethod =
    { Signature = signature; Body = guardBlock body }

/// Converts an entire model to guarded views.
let guard (model : Model<ModellerMethod, _>) : Model<GuarderMethod, _> =
    mapAxioms guardMethod model
