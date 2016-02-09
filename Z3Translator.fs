/// The part of the Z3 backend that translates terms to Z3.
module Starling.Z3.Translator

open Microsoft
open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Reifier
open Starling.Optimiser
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

/// Produces a map of substitutions that transform the parameters of a
/// vdef into the arguments of its usage.
let generateParamSubs {Params = dpars} {Params = vpars} =
    (* For every matching line in the view and viewdef, run
     * through the parameters creating substitution pairs.
     *)
    Seq.map2 (fun (_, name) up -> name, up) dpars vpars
    |> Map.ofSeq

/// Produces a variable substitution function table given a map of parameter
/// substitutions.
let paramSubFun vsubs =
    // TODO(CaptainHayashi): make this type-safe.
    // TODO(CaptainHayashi): maybe have a separate Const leg for params.
    {AVSub =
        function
        | Unmarked p as up ->
            match (Map.tryFind p vsubs) with
            | Some (AExpr e) -> e
            | Some _ -> failwith "param substitution type error"
            | None -> AConst up
        | q -> AConst q
     BVSub =
        function
        | Unmarked p as up ->
            match (Map.tryFind p vsubs) with
            | Some (BExpr e) -> e
            | Some _ -> failwith "param substitution type error"
            | None -> BConst up
        | q -> BConst q
    }

/// Produces the reification of an unguarded view with regards to a
/// given view definition.
/// This corresponds to D in the theory.
let instantiateDef model ufunc {View = vs; Def = e} =
    // Make sure our view expression is actually definite.
    match e with
    | Some ee ->
        (* First, we figure out the mapping from viewdef parameters to
         * actual view expressions.
         *)
        let vsubs = generateParamSubs vs ufunc

        ee
        (* We find all the changed parameters and substitute their
         * expansions.  We assume accidental capturing is impossible due to
         * disjointness checks on viewdefs vs. local variables, and freshness on
         * frame instantiations.
         *
         * Note that the global-add stage means that the expansions include the
         * global variables, so we need not treat them specially.
         *)
        |> boolSubVars (paramSubFun vsubs)
        |> ok
    | _ -> IndefiniteConstraint vs |> fail

/// Produces the reification of an unguarded func.
/// This corresponds to D^ in the theory.
let reifyZUnguarded model func =
    match List.tryFind (fun {View = {Name = n}} -> n = func.Name) model with
    | Some vdef -> instantiateDef model func vdef
    | None -> ok BTrue

let reifyZSingle model {Cond = c; Item = i} =
    reifyZUnguarded model i
    |> lift (mkImplies c)

/// Instantiates an entire view application over the given defining views.
let reifyZView model =
    Multiset.toSeq
    >> Seq.map (reifyZSingle model)
    >> collect
    >> lift Seq.toList
    >> lift mkAnd

/// Instantiates all of the views in a term over the given model.
let instantiateZTerm vdefs =
    tryMapTerm ok (reifyZView vdefs) (reifyZUnguarded vdefs)

/// Reifies all of the views in a term over the given defining model.
let reifyZTerm ctx vdefs : STerm<GView, VFunc> -> Result<FTerm, Error> =
    instantiateZTerm vdefs

/// Reifies all of the terms in a term list.
let reifyZ3 ctx model : Result<Model<FTerm, DFunc>, Error> =
    tryMapAxioms (reifyZTerm ctx (model.ViewDefs)) model

/// Combines the components of a reified term.
let combineTerm (ctx: Z3.Context) {Cmd = c; WPre = w; Goal = g} =
    (* This is effectively asking Z3 to refute (c ^ w => g).
     *
     * This arranges to:
     *   - ¬(c^w => g) premise
     *   - ¬(¬(c^w) v g) def. =>
     *   - ((c^w) ^ ¬g) deMorgan
     *   - (c^w^¬g) associativity.
     *)
    boolToZ3 ctx (mkAnd [c ; w; mkNot g] )

/// Combines reified terms into a list of Z3 terms.
let combineTerms ctx = mapAxioms (combineTerm ctx)
