/// The part of the Z3 backend that translates terms to Z3.
module Starling.Z3.Translator

open Microsoft
open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Framer
open Starling.Errors.Z3.Translator

/// Converts a Starling arithmetic expression to a Z3 ArithExpr.
let rec arithToZ3 (ctx: Z3.Context) =
    function
    | AConst c -> c |> constToString |> ctx.MkIntConst :> Z3.ArithExpr
    | AInt i -> (i |> ctx.MkInt) :> Z3.ArithExpr
    | AAdd xs -> ctx.MkAdd (xs |> Seq.map (arithToZ3 ctx) |> Seq.toArray)
    | ASub xs -> ctx.MkSub (xs |> Seq.map (arithToZ3 ctx) |> Seq.toArray)
    | AMul xs -> ctx.MkMul (xs |> Seq.map (arithToZ3 ctx) |> Seq.toArray)
    | ADiv (x, y) -> ctx.MkDiv (arithToZ3 ctx x, arithToZ3 ctx y)

/// Converts a Starling Boolean expression to a Z3 ArithExpr.
and boolToZ3 (ctx : Z3.Context) =
    function
    | BConst c -> c |> constToString |> ctx.MkBoolConst
    | BTrue -> ctx.MkTrue ()
    | BFalse -> ctx.MkFalse ()
    | BAnd xs -> ctx.MkAnd (xs |> Seq.map (boolToZ3 ctx) |> Seq.toArray)
    | BOr xs -> ctx.MkOr (xs |> Seq.map (boolToZ3 ctx) |> Seq.toArray)
    | BImplies (x, y) -> ctx.MkImplies (boolToZ3 ctx x, boolToZ3 ctx y)
    | BEq (x, y) -> ctx.MkEq (exprToZ3 ctx x, exprToZ3 ctx y)
    | BGt (x, y) -> ctx.MkGt (arithToZ3 ctx x, arithToZ3 ctx y)
    | BGe (x, y) -> ctx.MkGe (arithToZ3 ctx x, arithToZ3 ctx y)
    | BLe (x, y) -> ctx.MkLe (arithToZ3 ctx x, arithToZ3 ctx y)
    | BLt (x, y) -> ctx.MkLt (arithToZ3 ctx x, arithToZ3 ctx y)
    | BNot x -> x |> boolToZ3 ctx |> ctx.MkNot

/// Converts a Starling expression to a Z3 Expr.
and exprToZ3 (ctx: Z3.Context) =
    function
    | BExpr b -> boolToZ3 ctx b :> Z3.Expr
    | AExpr a -> arithToZ3 ctx a :> Z3.Expr

/// Tries to look up a multiset View in the defining views dvs.
let findDefOfView dvs uviewm =
    // Why we do this is explained later.
    let uview = Multiset.toList uviewm
    (* We look up view-defs based on count of views and names of each
     * view in the def.
     *
     * Of course, this depends on us having ensured that there are no
     * errors in the view or its definition earlier.
     *)
    List.tryFind (fun {CViews = vdm} ->
        (* We need to do list operations on the multiset contents,
         * so convert both sides to a (sorted) list.  We rely on the
         * sortedness to make the next step sound.
         *)
        let vd = Multiset.toList vdm
        (* Do these two views have the same number of terms?
         * If not, using forall2 is an error.
         *)
        List.length vd = List.length uview && List.forall2 (fun d s -> d.Name = s.Name) vd uview) dvs

/// Generates a param substitution sequence for one func in a view.
/// The arguments are the defining func and view func respectively.
let generateFuncParamSub {Params = dpars} {Params = vpars} =
    Seq.map2 (fun (_, name) up -> name, up) dpars vpars

/// Produces a map of substitutions that transform the parameters of a
/// vdef into the arguments of its usage.
let generateParamSubs (dviewm : Multiset<ViewDef>) (uviewm : Multiset<View>) =
    (* Performing list operations on the multiset contents *should* be
     * sound, because both sides will appear in the same order.
     *)
    let dview = Multiset.toList dviewm
    let uview = Multiset.toList uviewm

    (* For every matching line in the view and viewdef, run
     * through the parameters creating substitution pairs.
     *)
    Seq.map2 generateFuncParamSub dview uview
    |> Seq.concat
    |> Map.ofSeq

/// Produces a variable substitution function table given a map of parameter
/// substitutions.
let paramSubFun vsubs =
    // TODO(CaptainHayashi): make this type-safe.
    // TODO(CaptainHayashi): maybe have a separate Const leg for params.
    {ASub =
        function
        | Unmarked p as up ->
            match (Map.tryFind p vsubs) with
            | Some (AExpr e) -> e
            | Some e -> failwith "param substitution type error"
            | None -> AConst up
        | q -> AConst q
     BSub =
        function
        | Unmarked p as up ->
            match (Map.tryFind p vsubs) with
            | Some (BExpr e) -> e
            | Some e -> failwith "param substitution type error"
            | None -> BConst up
        | q -> BConst q
    }

/// Produces the reification of an unguarded view with regards to a
/// given view definition.
/// This corresponds to D in the theory.
let instantiateDef ctx model marker uview {CViews = vs; CExpr = e} =
    // Make sure our view expression is actually definite.
    match e with
    | Some ee ->
        (* First, we figure out the mapping from viewdef parameters to
         * actual view expressions.
         *)
        let vsubs = generateParamSubs vs uview

        // And the list of globals:
        let globals = model.Globals |> Map.toSeq |> Seq.map fst |> Set.ofSeq

        ee
        (* We now do two substitution runs on the expression.
         * First, we find all the changed parameters and substitute their
         * expansions.  We assume accidental capturing is impossible due to
         * disjointness checks on viewdefs vs. local variables, and freshness on
         * frame instantiations.
         *)
        |> boolSubVars (paramSubFun vsubs)
        (* Then, we perform the global pre-or-post-state translation using model
         * and marker.
         *)
        |> boolMarkVars marker (inSet globals)
        (* Finally, convert to Z3. *)
        |> boolToZ3 ctx
        |> ok
    | _ -> IndefiniteConstraint vs |> fail

/// Produces the reification of an unguarded view multiset.
/// This corresponds to D^ in the theory.
let reifyZUnguarded ctx model marker uview =
    match findDefOfView model.DefViews uview with
    | Some vdef -> instantiateDef ctx model marker uview vdef
    | None -> ctx.MkTrue() |> ok

let reifyZSingle (ctx: Z3.Context) model marker {Cond = c; Item = i} =
    reifyZUnguarded ctx model marker i
    |> lift (fun zv -> ctx.MkImplies(boolToZ3 ctx c, zv))

/// Z3-reifies an entire view application over the given defining views.
/// Marks the globals in the resulting expression with the given marker.
let reifyZView (ctx: Z3.Context) model marker =
    Multiset.toSeq
    >> Seq.map (reifyZSingle ctx model marker)
    >> collect
    >> lift Seq.toArray
    >> lift (fun xs -> ctx.MkAnd xs)

/// Z3-reifies all of the views in a term over the given defining model.
let reifyZTerm ctx model term =
    (* This is also where we perform our final variable substitution,
     * converting all global variables to their pre-state in Pre, and
     * post-state in Post.
     *)
    lift2 (fun pre post ->
           { Conditions = { Pre = pre; Post = post }
             Inner = boolToZ3 ctx term.Inner })
          (reifyZView ctx model Before term.Conditions.Pre)
          (reifyZView ctx model After term.Conditions.Post)

/// Reifies all of the terms in a term list.
let reifyZ3 ctx model = Seq.map (reifyZTerm ctx model) >> collect

/// Combines the components of a reified term.
let combineTerm (ctx: Z3.Context) reterm =
    ctx.MkAnd [| reterm.Conditions.Pre
                 reterm.Inner
                 ctx.MkNot reterm.Conditions.Post |]

/// Combines reified terms into a list of Z3 terms.
let combineTerms ctx = List.map (combineTerm ctx)
