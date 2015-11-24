module Starling.Expander

open Starling.Model
open Starling.Utils
open Microsoft.Z3

/// Calculates the powerset of a set.
let powerset set =
    // TODO(CaptainHayashi): relocate to where this is used, or delete if not.
    Set.fold (fun ps s -> ps + Set.map (fun p -> s + p) ps) (new Set<Set<BoolExpr>> ( [Set.empty] )) set

/// Converts a view from conditional to guarded form.
/// This takes the Z3 context, and the set of all conditions forming the
/// suffix of any guards generated from this view.
let rec resolveCondViewIn (suffix: Set<BoolExpr>) (ctx: Context) cv =
    match cv with
    | CSetView v -> [ {GCond = suffix
                       GView = v} ]
    | CITEView (expr, tviews, fviews) ->
        List.concat [ resolveCondViewsIn (suffix.Add expr) ctx tviews
                      resolveCondViewsIn (suffix.Add (ctx.MkNot expr)) ctx fviews ]
/// Resolves a list of views, given a set of conditions held true.
and resolveCondViewsIn suffix ctx = concatMap (resolveCondViewIn suffix ctx)

/// Resolves a full condition-view list into a guarded-view multiset.
let resolveCondViews ctx = resolveCondViewsIn Set.empty ctx
