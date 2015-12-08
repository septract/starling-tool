/// The part of the Starling process that reifies Terms into Z3 predicates.
module Starling.Reifier

open Microsoft

open Starling.Z3
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Converts a GuarView to a tuple.
let tupleOfGuarView gv = (gv.GCond, gv.GView)

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
let reifyUnguarded model uview =
    // This corresponds to D^ in the theory.
    let ctx = model.Context

    let uv = List.sort uview

    match findDefOfView model uv with
    | Some vdef -> instantiateDef ctx uv vdef
    | None -> ctx.MkTrue ()

/// Reifies a single GuarView.
let reifySingle model view =
    let ctx = model.Context

    (* This corresponds to Dlift in the theory.
     * Our end goal is the term (implies (and guars...) vrs),
     * where vrs is defined below.
     *)

    // First, pull the guards and views out of the view.
    let guars, views =
        view
        |> List.map tupleOfGuarView
        |> List.unzip

    // We reify the view in a separate function.
    let vr = reifyUnguarded model views
    let vrs = vr.Simplify () :?> Z3.BoolExpr

    let gr = ctx.MkAnd (Array.ofList guars)
    let grs = gr.Simplify () :?> Z3.BoolExpr
    mkImplies ctx grs vrs

/// Produces the power-multiset of a multiset (list).
let powermultiset ms =
    (* Solve the problem using Boolean arithmetic on the index of the
     * powerset item.
     *)
    seq {for i in 0 .. (1 <<< List.length ms) - 1 do
             yield (seq {0 .. (List.length ms) - 1}
                    |> Seq.choose (fun j ->
                                       let cnd: int = i &&& (1 <<< j)
                                       if cnd <> 0
                                       then Some ms.[j]
                                       else None)) }
    

/// Reifies an entire view application.
let reifyView model vapp =
    model.Context.MkAnd (vapp
                         |> powermultiset
                         |> Seq.map (List.ofSeq >> reifySingle model)
                         |> Seq.toArray)

/// Reifies all of the views in a term.
let reifyTerm model term =
    (* This is also where we perform our final variable substitution,
     * converting all global variables to their pre-state in TPre, and
     * post-state in TPost.
     *)
    let tpre = reifyView model term.TPre
    let tpost = reifyView model term.TPost

    {TPre = subAllInEnv model.Globals envVarToBefore (tpre :> Z3.Expr)
            :?> Z3.BoolExpr
     TAction = term.TAction
     TPost = subAllInEnv model.Globals envVarToAfter (tpost :> Z3.Expr)
             :?> Z3.BoolExpr}

/// Reifies all of the terms in a term list.
let reify model = List.map (reifyTerm model)

/// Combines the components of a reified term.
let combineTerm model reterm =
    let ctx = model.Context
    ctx.MkAnd [|reterm.TPre
                reterm.TAction
                ctx.MkNot (reterm.TPost)|]

/// Combines reified terms into a list of Z3 terms.
let combineTerms model = List.map (combineTerm model)

/// Reifies and combines terms into a Z3 query.
let reifyZ3 model = reify model >> combineTerms model
