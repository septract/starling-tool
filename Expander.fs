module Starling.Expander

open Starling.Model
open Starling.Utils
open Microsoft.Z3

/// Given a CondView, generates the set of unique Z3 expressions switching
/// views in the CondView.
let rec decisions view =
    match view with
    | CSetView v -> Set.empty
    | CITEView (e, l, r) -> new Set<BoolExpr> ( [e] ) + allDecisions l + allDecisions r
and allDecisions = List.map decisions >> Set.unionMany

/// Calculates the powerset of a set.
let powerset set =
    Set.fold (fun ps s -> ps + Set.map (fun p -> s + p) ps) (new Set<Set<BoolExpr>> ( [Set.empty] )) set

/// Resolves a view, given a set of conditions held true.
/// This resolves every CITEView by taking the true path if the condition is
/// in the set, and the false path otherwise.
/// The result is the list of views active given the conditions.
let rec resolveCondView (trueConds: Set<BoolExpr>) cv =
    match cv with
    | CSetView v -> [v]
    | CITEView (expr, tviews, fviews) -> resolveCondViews trueConds
                                                          (if (trueConds.Contains expr)
                                                           then tviews
                                                           else fviews)
/// Resolves a list of views, given a set of conditions held true.
and resolveCondViews trueConds = concatMap (resolveCondView trueConds)

/// Converts a CondView-list to a list of pairs of views and assumed conditions.
let flattenCondView cv =
    (* The high-level idea behind this is:
     * - Traverse the precondition of the axiom, making a set of all conditions
     *   used to switch views in the precondition;
     * - Generate the powerset of this set;
     * - Convert the powerset to a list;
     * - For every item in the powerset, traverse the 
     *)
    0

