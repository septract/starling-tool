/// <summary>
///     The part of the language frontend that desugars conditional
///     (if-then-else) views to guarded views.
/// </summary>
module Starling.Lang.Guarder

open Starling.Collections
open Starling.Utils
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Lang.AST
open Starling.Lang.Modeller
open Starling.Lang.ViewDesugar

[<AutoOpen>]
module Types =
    type GuarderView = IteratedGView<Sym<Var>>
    type GuarderViewExpr = ViewExpr<GuarderView>
    type GuarderPartCmd = PartCmd<GuarderViewExpr>
    type GuarderBlock = FullBlock<GuarderViewExpr, GuarderPartCmd>

/// Resolves a full condition-view multiset into a guarded-view multiset.
let guardCView (cview : CView) : GuarderView =
    let rec guardCFuncIn suffix cv =
        match cv.Func with
        | CFunc.Func v ->
            (* Treat non-iterated views as if they have the iterator [1].
               This means we don't need to special-case them elsewhere. *)
            [ { Func = { Cond = mkAnd (Set.toList suffix); Item = v };
                Iterator = maybe (IInt 1L) IVar cv.Iterator } ]
        | CFunc.ITE(expr, tviews, fviews) ->
            List.concat
                [ guardCViewIn (suffix.Add expr) (Multiset.toFlatList tviews)
                  guardCViewIn (suffix.Add (mkNot expr))
                      (Multiset.toFlatList fviews) ]
    and guardCViewIn suffix = concatMap (guardCFuncIn suffix)

    // TODO(CaptainHayashi): woefully inefficient.
    let guarded = guardCViewIn Set.empty (Multiset.toFlatList cview)
    Multiset.ofFlatList guarded

/// Resolves a full condition-view ViewExpr into a guarded-view multiset.
let guardCViewExpr : ModellerViewExpr -> GuarderViewExpr =
    function
    | Mandatory v -> Mandatory (guardCView v)
    | Advisory v -> Advisory (guardCView v)

/// Converts a viewed command to guarded views.
let rec guardViewedCommand (vc : ModellerPartCmd * ModellerViewExpr)
  : (GuarderPartCmd * GuarderViewExpr) =
    pairMap guardPartCmd guardCViewExpr vc

/// Converts a block to guarded views.
and guardBlock
  ({Pre = pre; Cmds = contents} : ModellerBlock)
  : GuarderBlock =
    { Pre = guardCViewExpr pre
      Cmds = List.map guardViewedCommand contents }

/// Converts a PartCmd to guarded views.
and guardPartCmd : ModellerPartCmd -> GuarderPartCmd =
    function
    | Prim p -> Prim p
    | While (isDo, expr, inner) ->
        While (isDo, expr, guardBlock inner)
    | ITE (expr, inTrue, inFalse) ->
        ITE (expr, guardBlock inTrue, Option.map guardBlock inFalse)

/// Converts an entire model to guarded views.
let guard (model : Model<ModellerBlock, ViewDefiner<SVBoolExpr option>>) : Model<GuarderBlock, ViewDefiner<SVBoolExpr option>> =
    mapAxioms guardBlock model
