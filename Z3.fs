/// <summary>
///     Expression translation and runners for Z3.
/// </summary>
module Starling.Core.Z3

open Microsoft
open Starling.Core.Expr
open Starling.Core.TypeSystem


/// <summary>
///     Pretty printers for the Z3 types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// Pretty-prints Z3 expressions.
    let printZ3Exp (expr : #Z3.Expr) = String(expr.ToString())

    /// Pretty-prints a satisfiability result.
    let printSat (sat : Z3.Status) : Doc =
        match sat with
        (* Remember: we're trying to _refute_ the proof term with Z3.
           Thus, sat is what we're trying to _avoid_ here. *)
        | Z3.Status.SATISFIABLE -> error (String "fail")
        | Z3.Status.UNSATISFIABLE -> success (String "success")
        | _ -> inconclusive (String "unknown")


/// <summary>
///     Functions for translating Starling expressions into Z3.
/// </summary>
module Expr =
    /// <summary>
    ///     Converts a type into a Z3 sort.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">The Z3 context to use to generate the sorts.</param>
    /// <param name="ty">The type to convert to a sort.</param>
    /// <returns>
    ///     The Z3 sort corresponding to <paramref name="ty"/>.
    /// </returns>
    let rec typeToSort (reals : bool) (ctx : Z3.Context) (ty : Type) : Z3.Sort =
        match ty with
        | AnInt when reals -> ctx.MkRealSort () :> Z3.Sort
        | AnInt -> ctx.MkIntSort () :> Z3.Sort
        | ABool -> ctx.MkBoolSort () :> Z3.Sort
        | AnArray (eltype, _) ->
            let elZ3 = typeToSort reals ctx eltype
            ctx.MkArraySort (range = ctx.MkIntSort (), domain = elZ3) :> Z3.Sort

    /// Converts a Starling arithmetic expression to a Z3 ArithExpr.
    let rec intToZ3
      (reals : bool)
      (toStr : 'Var -> string)
      (ctx : Z3.Context)
      (int : TypedIntExpr<'Var>) : Z3.ArithExpr =
        let rec iz =
            function
            | IVar c when reals -> c |> toStr |> ctx.MkRealConst :> Z3.ArithExpr
            | IVar c -> c |> toStr |> ctx.MkIntConst :> Z3.ArithExpr
            | IIdx (arr, idx) ->
                // TODO(CaptainHayashi): ensure eltype is Int?
                let arrZ3 = arrayToZ3 reals toStr ctx arr
                let idxZ3 = intToZ3 reals toStr ctx (mkTypedSub normalRec idx)
                // TODO(CaptainHayashi): make this not crash if the select is not an ArithExpr.
                ctx.MkSelect (arrZ3, idxZ3) :?> Z3.ArithExpr
            | IInt i when reals -> (i |> ctx.MkReal) :> Z3.ArithExpr
            | IInt i -> (i |> ctx.MkInt) :> Z3.ArithExpr
            | IAdd xs -> ctx.MkAdd (xs |> Seq.map iz |> Seq.toArray)
            | ISub xs -> ctx.MkSub (xs |> Seq.map iz |> Seq.toArray)
            | IMul xs -> ctx.MkMul (xs |> Seq.map iz |> Seq.toArray)
            | IDiv (x, y) -> ctx.MkDiv (iz x, iz y)
            // TODO(CaptainHayashi): refuse AMod when reals is true.
            | IMod (x, y) -> ctx.MkMod (iz x :?> Z3.IntExpr, iz y :?> Z3.IntExpr) :> Z3.ArithExpr
        iz (stripTypeRec int)

    /// Converts a Starling Boolean expression to a Z3 ArithExpr.
    and boolToZ3
      (reals : bool)
      (toStr : 'Var -> string)
      (ctx: Z3.Context)
      (bool : TypedBoolExpr<'Var>) : Z3.BoolExpr =
        let iz x = intToZ3 reals toStr ctx x
        let ez = exprToZ3 reals toStr ctx

        let rec bz =
            function
            | BVar c -> c |> toStr |> ctx.MkBoolConst
            | BIdx (arr, idx) ->
                // TODO(CaptainHayashi): ensure eltype is Bool?
                let arrZ3 = arrayToZ3 reals toStr ctx arr
                let idxZ3 = intToZ3 reals toStr ctx (mkTypedSub normalRec idx)
                // TODO(CaptainHayashi): make this not crash if the select is not a BoolExpr.
                ctx.MkSelect (arrZ3, idxZ3) :?> Z3.BoolExpr
            | BTrue -> ctx.MkTrue ()
            | BFalse -> ctx.MkFalse ()
            | BAnd xs -> ctx.MkAnd (xs |> Seq.map bz |> Seq.toArray)
            | BOr xs -> ctx.MkOr (xs |> Seq.map bz |> Seq.toArray)
            | BImplies (x, y) -> ctx.MkImplies (bz x, bz y)
            | BEq (x, y) -> ctx.MkEq (ez x, ez y)
            | BGt (x, y) -> ctx.MkGt (iz x, iz y)
            | BGe (x, y) -> ctx.MkGe (iz x, iz y)
            | BLe (x, y) -> ctx.MkLe (iz x, iz y)
            | BLt (x, y) -> ctx.MkLt (iz x, iz y)
            | BNot x -> x |> bz |> ctx.MkNot
        bz (stripTypeRec bool)

    /// Converts a Starling array expression to a Z3 Expr.
    and arrayToZ3
      (reals : bool)
      (toStr : 'Var -> string)
      (ctx: Z3.Context)
      (arr : TypedArrayExpr<'Var>)
      : Z3.ArrayExpr =
        let eltype = arr.SRec.ElementType

        match stripTypeRec arr with
        | AVar c ->
            ctx.MkArrayConst
                (name = toStr c,
                 domain = ctx.MkIntSort (),
                 range = typeToSort reals ctx eltype)
        | AIdx (arr',  idx) ->
            // TODO(CaptainHayashi): ensure eltype is Array?
            let arrZ3 = arrayToZ3 reals toStr ctx arr'
            let idxZ3 = intToZ3 reals toStr ctx (mkTypedSub normalRec idx)
            // TODO(CaptainHayashi): make this not crash if the select is not an ArrayExpr.
            ctx.MkSelect (arrZ3, idxZ3) :?> Z3.ArrayExpr
        | AUpd (arr', idx, upd) ->
            let arrZ3 = arrayToZ3 reals toStr ctx (updateTypedSub arr arr')
            let idxZ3 = intToZ3 reals toStr ctx (mkTypedSub normalRec idx)
            let updZ3 = exprToZ3 reals toStr ctx upd
            ctx.MkStore (arrZ3, idxZ3, updZ3)


    /// Converts a Starling expression to a Z3 Expr.
    and exprToZ3
      (reals : bool)
      (toStr : 'Var -> string)
      (ctx: Z3.Context)
      (expr : Expr<'Var>)
      : Z3.Expr =
        match expr with
        | Expr.Bool (t, b) -> boolToZ3 reals toStr ctx (mkTypedSub t b) :> Z3.Expr
        | Expr.Int (t, i) -> intToZ3 reals toStr ctx (mkTypedSub t i) :> Z3.Expr
        | Expr.Array (t, a) -> arrayToZ3 reals toStr ctx (mkTypedSub t a) :> Z3.Expr

    /// <summary>
    ///     Z3 tests for expressions.
    /// </summary>
    module Tests =
        // TODO(CaptainHayashi): move this to a separate module.

        open NUnit.Framework
        open Starling.Utils.Testing

        [<Test>]
        let ``modulo expressions are translated correctly when reals is disabled`` () =
            use ctx = new Z3.Context ()
            assertEqual
                (ctx.MkMod (ctx.MkIntConst "foo", ctx.MkInt 5L) :> Z3.ArithExpr)
                (intToZ3 false id ctx (normalInt (mkMod (IVar "foo") (IInt 5L))))

/// <summary>
///     Z3 invocation.
/// </summary>
module Run =
    /// <summary>
    ///     Runs Z3 on a single Boolean Z3 expression.
    /// </summary>
    let runTerm (ctx: Z3.Context) term =
        let solver = ctx.MkSimpleSolver()
        solver.Assert [| term |]
        solver.Check [||]
