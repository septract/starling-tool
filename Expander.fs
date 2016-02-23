module Starling.Lang.Expander

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Utils
open Starling.Lang.Modeller

/// Converts a view from conditional to guarded form.
/// This takes the set of all conditions forming the suffix of any guards
/// generated from this view.
let rec resolveCondViewIn (suffix : Set<BoolExpr>) = 
    function 
    | Func v -> 
        [ { Cond = 
                suffix
                |> Set.toList
                |> mkAnd
            Item = v } ]
    | CFunc.ITE(expr, tviews, fviews) -> 
        List.concat [ resolveCondViewsIn (suffix.Add expr) (Multiset.toList tviews)
                      resolveCondViewsIn (suffix.Add(mkNot expr)) (Multiset.toList fviews) ]

/// Resolves a list of views, given a set of conditions held true.
and resolveCondViewsIn suffix = concatMap (resolveCondViewIn suffix)

/// Resolves a full condition-view multiset into a guarded-view multiset.
let resolveCondViews = 
    // TODO(CaptainHayashi): woefully inefficient.
    Multiset.toList
    >> resolveCondViewsIn Set.empty 
    >> Multiset.ofList

/// Expands an axiom.
let expandAxiom { Pre = pre; Post = post; Cmd = i } = 
    { Pre = resolveCondViews pre
      Post = resolveCondViews post
      Cmd = i }

/// Expands an entire model.
let expand : Model<PAxiom<CView>, DView> -> Model<PAxiom<GView>, DView> = mapAxioms expandAxiom
