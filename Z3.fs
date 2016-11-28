/// <summary>
///     Expression translation and runners for Z3.
/// </summary>
module Starling.Core.Z3

open Microsoft
open Starling.Core.Expr


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
    /// Converts a Starling arithmetic expression to a Z3 ArithExpr.
    let rec intToZ3
      (reals : bool)
      (toStr : 'var -> string)
      (ctx: Z3.Context)
      (int : IntExpr<'var>) : Z3.ArithExpr =
        let rec iz =
            function
            | IVar c when reals -> c |> toStr |> ctx.MkRealConst :> Z3.ArithExpr
            | IVar c -> c |> toStr |> ctx.MkIntConst :> Z3.ArithExpr
            | IInt i when reals -> (i |> ctx.MkReal) :> Z3.ArithExpr
            | IInt i -> (i |> ctx.MkInt) :> Z3.ArithExpr
            | IAdd xs -> ctx.MkAdd (xs |> Seq.map iz |> Seq.toArray)
            | ISub xs -> ctx.MkSub (xs |> Seq.map iz |> Seq.toArray)
            | IMul xs -> ctx.MkMul (xs |> Seq.map iz |> Seq.toArray)
            | IDiv (x, y) -> ctx.MkDiv (iz x, iz y)
            // TODO(CaptainHayashi): refuse AMod when reals is true.
            | IMod (x, y) -> ctx.MkMod (iz x :?> Z3.IntExpr, iz y :?> Z3.IntExpr) :> Z3.ArithExpr
        iz int

    /// Converts a Starling Boolean expression to a Z3 ArithExpr.
    and boolToZ3
      (reals : bool)
      (toStr : 'var -> string)
      (ctx: Z3.Context)
      (bool : BoolExpr<'var>) : Z3.BoolExpr =
        let az = intToZ3 reals toStr ctx
        let ez = exprToZ3 reals toStr ctx

        let rec bz =
            function
            | BVar c -> c |> toStr |> ctx.MkBoolConst
            | BTrue -> ctx.MkTrue ()
            | BFalse -> ctx.MkFalse ()
            | BAnd xs -> ctx.MkAnd (xs |> Seq.map bz |> Seq.toArray)
            | BOr xs -> ctx.MkOr (xs |> Seq.map bz |> Seq.toArray)
            | BImplies (x, y) -> ctx.MkImplies (bz x, bz y)
            | BEq (x, y) -> ctx.MkEq (ez x, ez y)
            | BGt (x, y) -> ctx.MkGt (az x, az y)
            | BGe (x, y) -> ctx.MkGe (az x, az y)
            | BLe (x, y) -> ctx.MkLe (az x, az y)
            | BLt (x, y) -> ctx.MkLt (az x, az y)
            | BNot x -> x |> bz |> ctx.MkNot
        bz bool

    /// Converts a Starling expression to a Z3 Expr.
    and exprToZ3
      (reals : bool)
      (toStr : 'var -> string)
      (ctx: Z3.Context)
      : Expr<'var> -> Z3.Expr =
        function
        | Expr.Bool b -> boolToZ3 reals toStr ctx b :> Z3.Expr
        | Expr.Int a -> intToZ3 reals toStr ctx a :> Z3.Expr

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
                (intToZ3 false id ctx (mkMod (IVar "foo") (IInt 5L)))

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
