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
let rec resolveCondView (ctx: Context) (suffix: Set<BoolExpr>) cv =
    match cv with
    | CSetView v -> [(suffix, v)]
    | CITEView (expr, tviews, fviews) ->
        List.concat [ resolveCondViews ctx (suffix.Add expr) tviews
                      resolveCondViews ctx (suffix.Add (ctx.MkNot expr)) fviews ]
/// Resolves a list of views, given a set of conditions held true.
and resolveCondViews ctx suffix = concatMap (resolveCondView ctx suffix)
