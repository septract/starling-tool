module Starling.Lang.Guarder

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Utils
open Starling.Lang.Modeller

/// Converts a func from conditional to guarded form.
/// This takes the set of all conditions forming the suffix of any guards
/// generated from this view.
let rec guardCFuncIn (suffix : Set<BoolExpr>) = 
    function 
    | CFunc.Func v -> 
        [ { Cond = 
                suffix
                |> Set.toList
                |> mkAnd
            Item = v } ]
    | CFunc.ITE(expr, tviews, fviews) -> 
        List.concat [ guardCViewIn (suffix.Add expr) (Multiset.toList tviews)
                      guardCViewIn (suffix.Add(mkNot expr)) (Multiset.toList fviews) ]

/// Resolves a list of views, given a set of conditions held true.
and guardCViewIn suffix = concatMap (guardCFuncIn suffix)

/// Resolves a full condition-view multiset into a guarded-view multiset.
let guardCView : CView -> GView = 
    // TODO(CaptainHayashi): woefully inefficient.
    Multiset.toList
    >> guardCViewIn Set.empty 
    >> Multiset.ofList

/// Converts the inner axiom in a structured leg to guarded views.
let rec guardInnerAxiom {Pre = pre; Post = post; Cmd = cmd} =
    { Pre = guardCView pre
      Post = guardCView post
      Cmd = List.map guardAxiom cmd }

/// Converts a PartCmd to guarded views.
and guardPartCmd : PartCmd<CView> -> PartCmd<GView> =
    function
    | Prim p -> Prim p
    | While (isDo, expr, inner) ->
        While (isDo, expr, guardInnerAxiom inner)
    | ITE (expr, inTrue, inFalse) ->
        ITE (expr, guardInnerAxiom inTrue, guardInnerAxiom inFalse)

/// Converts an axiom to guarded views.
and guardAxiom { Pre = pre; Post = post; Cmd = cmd } = 
    { Pre = guardCView pre
      Post = guardCView post
      Cmd = guardPartCmd cmd }

/// Converts an entire model to guarded views.
let guard : Model<Axiom<CView, PartCmd<CView>>, DView> -> Model<Axiom<GView, PartCmd<GView>>, DView> =
    mapAxioms guardAxiom
