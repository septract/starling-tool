module Starling.Expander

open Starling.Collections
open Starling.Z3
open Starling.Model
open Starling.Utils
open Microsoft.Z3

/// Converts a view from conditional to guarded form.
/// This takes the Z3 context, and the set of all conditions forming the
/// suffix of any guards generated from this view.
let rec resolveCondViewIn (suffix : Set<BoolExpr>) (ctx : Context) = 
    function 
    | Func v -> 
        [ { Cond = 
                suffix
                |> Set.toArray
                |> mkAnd ctx
            Item = v } ]
    | ITE(expr, tviews, fviews) -> 
        List.concat [ resolveCondViewsIn (suffix.Add expr) ctx (Multiset.toList tviews)
                      resolveCondViewsIn (suffix.Add(ctx.MkNot expr)) ctx (Multiset.toList fviews) ]

/// Resolves a list of views, given a set of conditions held true.
and resolveCondViewsIn suffix ctx = concatMap (resolveCondViewIn suffix ctx)

/// Resolves a full condition-view multiset into a guarded-view multiset.
let resolveCondViews ctx = 
    // TODO(CaptainHayashi): woefully inefficient.
    Multiset.toList
    >> resolveCondViewsIn Set.empty ctx
    >> Multiset.ofList

/// Expands a condition pair.
let expandCondPair ctx { Pre = pre; Post = post } = 
    { Pre = resolveCondViews ctx pre
      Post = resolveCondViews ctx post }

/// Expands an axiom.
let expandAxiom ctx { Conditions = cs; Inner = i } = 
    { Conditions = expandCondPair ctx cs
      Inner = i }

/// Expands a list of axioms.
let expandAxioms ctx = List.map (expandAxiom ctx)

/// Expands an entire model.
let expand (model : FlatModel) = withAxioms (expandAxioms model.Context model.Axioms) model
