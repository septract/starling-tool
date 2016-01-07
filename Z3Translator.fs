/// The part of the Z3 backend that translates terms to Z3.
module Starling.Z3.Translator

open Microsoft
open Starling
open Starling.Collections
open Starling.Model
open Starling.Framer
open Starling.Semantics

/// Tries to look up a multiset View in the defining views.
let findDefOfView model uviewm = 
    // Why we do this is explained later.
    let uview = Multiset.toList uviewm
    (* We look up view-defs based on count of views and names of each
     * view in the def.  
     *
     * Of course, this depends on us having ensured that there are no
     * errors in the view or its definition earlier.
     *)
    List.tryFind (fun vdm -> 
        (* We need to do list operations on the multiset contents,
         * so convert both sides to a (sorted) list.  We rely on the
         * sortedness to make the next step sound.
         *)
        let vd = Multiset.toList vdm.CViews
        (* Do these two views have the same number of terms?
         * If not, using forall2 is an error.
         *)
        List.length vd = List.length uview && List.forall2 (fun d s -> d.Name = s.Name) vd uview) model.DefViews

/// Produces a map of substitutions that transform the parameters of a
/// vdef into the arguments of its usage.
let generateParamSubs (ctx : Z3.Context) (dviewm : Multiset<ViewDef>) (uviewm : Multiset<View>) : (Z3.Expr * Z3.Expr) list = 
    (* Performing list operations on the multiset contents *should* be
     * sound, because both sides will appear in the same order.
     *)
    let dview = Multiset.toList dviewm
    let uview = Multiset.toList uviewm
    List.fold2 
        ((* For every matching line in the view and viewdef, run
         * through the parameters creating substitution pairs.
         *)
         fun subs dv uv -> 
        List.fold2 (fun s (ty, name : string) up -> (ctx.MkConst(name, typeToSort ctx ty), up :> Z3.Expr) :: s) subs 
            dv.Params uv.Params) [] dview uview

/// Produces the reification of an unguarded view with regards to a
/// given view definition.
/// This corresponds to D in the theory.
let instantiateDef ctx uview vdef = 
    (* First, we figure out the mapping from viewdef parameters to
     * actual view expressions.
     *)
    let vsubs = generateParamSubs ctx vdef.CViews uview
    (* Then, we can substitute the view-application parameters into the
     * view definition's Z3 expression.  We assume accidental capturing
     * is impossible due to disjointness checks on viewdefs vs. local
     * variables, and freshness on frame instantiations.
     *)
    List.fold 
        (fun (expr : Z3.BoolExpr) (sfrom : Z3.Expr, sto : Z3.Expr) -> (expr.Substitute(sfrom, sto)) :?> Z3.BoolExpr) 
        vdef.CZ3 vsubs

/// Produces the reification of an unguarded view multiset.
/// This corresponds to D^ in the theory.
let reifyZUnguarded ctx uview = 
    match findDefOfView model uview with
    | Some vdef -> instantiateDef ctx uview vdef
    | None -> ctx.MkTrue()

let reifyZSingle ctx {Cond = c; Item = i} = 
    mkImplies ctx c (reifyZUnguarded model i)

/// Z3-reifies an entire view application.
let reifyZView ctx = 
    Multiset.toSeq
    >> Seq.map (reifyZSingle ctx)
    >> mkAnd ctx

/// Z3-reifies all of the views in a term.
let reifyZTerm ctx term = 
    (* This is also where we perform our final variable substitution,
     * converting all global variables to their pre-state in Pre, and
     * post-state in Post.
     *)
    let tpre = reifyZView ctx term.Conditions.Pre
    let tpost = reifyZView ctx term.Conditions.Post
    { Conditions = 
          { Pre = Expr.subAllInEnv model.Globals Expr.envVarToBefore (tpre :> Z3.Expr) :?> Z3.BoolExpr
            Post = Expr.subAllInEnv model.Globals Expr.envVarToAfter (tpost :> Z3.Expr) :?> Z3.BoolExpr }
      Inner = term.Inner }

/// Reifies all of the terms in a term list.
let reifyZ3 ctx = List.map (reifyZTerm ctx)

/// Combines the components of a reified term.
let combineTerm ctx reterm = 
    mkAnd ctx [ reterm.Conditions.Pre
                reterm.Inner
                mkNot ctx (reterm.Conditions.Post) ]

/// Combines reified terms into a list of Z3 terms.
let combineTerms ctx = List.map (combineTerm ctx)
