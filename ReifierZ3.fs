/// The part of the Starling process that finishes the reification
/// towards Z3 predicates.
module Starling.ReifierZ3

open Microsoft

open Starling.Z3
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Tries to look up a multiset View in the defining views.
let findDefOfView model uview =
    (* We look up view-defs based on count of views and names of each
     * view in the def.  
     *
     * Of course, this depends on us having ensured that there are no
     * errors in the view or its definition earlier.
     *)
    List.tryFind
        (fun vd ->
            (* Do these two views have the same number of terms?
             * If not, using forall2 is an error.
             *)
            List.length vd.CViews = List.length uview
            && List.forall2 (fun d s -> d.VName = s.VName)
                            vd.CViews
                            uview)
        model.DefViews

/// Produces a map of substitutions that transform the parameters of a
/// vdef into the arguments of its usage.
let generateParamSubs (ctx: Z3.Context)
                      (dview: ViewDef list)
                      (uview: View list): (Z3.Expr * Z3.Expr) list =
    List.fold2
        (* For every matching line in the view and viewdef, run
         * through the parameters creating substitution pairs.
         *)
        (fun subs dv uv ->
            List.fold2
                (fun s (ty, name: string) up -> (ctx.MkConst (name, typeToSort ctx ty),
                                                 up :> Z3.Expr) :: s)
                subs
                dv.VParams
                uv.VParams)
        []
        dview
        uview

/// Produces the reification of an unguarded view with regards to a
/// given view definition.
let instantiateDef ctx uview vdef =
    // This corresponds to D in the theory.

    (* First, we figure out the mapping from viewdef parameters to
     * actual view expressions.
     *)
    let vsubs = generateParamSubs ctx vdef.CViews uview

    (* Then, we can substitute the view-application parameters into the
     * view definition's Z3 expression.  We assume accidental capturing
     * is impossible due to disjointness checks on viewdefs vs. local
     * variables, and freshness on frame instantiations.
     *)
    List.fold (fun (expr: Z3.BoolExpr) (sfrom: Z3.Expr, sto: Z3.Expr) ->
                   (expr.Substitute (sfrom, sto)) :?> Z3.BoolExpr)
        vdef.CZ3
        vsubs

/// Produces the reification of an unguarded view multiset.
let reifyZUnguarded model uview =
    // This corresponds to D^ in the theory.
    let ctx = model.Context

    let uv = List.sort uview

    match findDefOfView model uv with
    | Some vdef -> instantiateDef ctx uv vdef
    | None -> ctx.MkTrue ()

let reifyZSingle model view =
    let ctx = model.Context
    mkImplies ctx view.GCond (reifyZUnguarded model view.GItem)

/// Z3-reifies an entire view application.
let reifyZView model vapp =
    model.Context.MkAnd (vapp
                         |> List.map (reifyZSingle model)
                         |> List.toArray)

/// Z3-reifies all of the views in a term.
let reifyZTerm model term =
    (* This is also where we perform our final variable substitution,
     * converting all global variables to their pre-state in Pre, and
     * post-state in Post.
     *)
    let tpre = reifyZView model term.Conditions.Pre
    let tpost = reifyZView model term.Conditions.Post

    {Conditions = {Pre = subAllInEnv model.Globals envVarToBefore (tpre :> Z3.Expr)
                         :?> Z3.BoolExpr
                   Post = subAllInEnv model.Globals envVarToAfter (tpost :> Z3.Expr)
                          :?> Z3.BoolExpr}
     Inner = term.Inner}

/// Reifies all of the terms in a term list.
let reifyZ3 model = List.map (reifyZTerm model)

/// Combines the components of a reified term.
let combineTerm model reterm =
    let ctx = model.Context
    ctx.MkAnd [|reterm.Conditions.Pre
                reterm.Inner
                ctx.MkNot (reterm.Conditions.Post)|]

/// Combines reified terms into a list of Z3 terms.
let combineTerms model = List.map (combineTerm model)