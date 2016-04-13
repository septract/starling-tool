/// <summary>
///     Expression translation and runners for Z3.
/// </summary>
module Starling.Core.Z3

open Microsoft
open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core.Expr


/// <summary>
///     Pretty printers for the Z3 types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// Pretty-prints Z3 expressions.
    let printZ3Exp (expr : #Z3.Expr) = String(expr.ToString())

    /// Pretty-prints a satisfiability result.
    let printSat =
        function
        | Z3.Status.SATISFIABLE -> "fail"
        | Z3.Status.UNSATISFIABLE -> "success"
        | _ -> "unknown"
        >> String


/// <summary>
///     Functions for translating Starling expressions into Z3.
/// </summary>
module Expr =
    /// Converts a Starling arithmetic expression to a Z3 ArithExpr.
    let rec arithToZ3 reals (ctx: Z3.Context) =
        function
        | AConst c when reals -> c |> constToString |> ctx.MkRealConst :> Z3.ArithExpr
        | AConst c -> c |> constToString |> ctx.MkIntConst :> Z3.ArithExpr
        | AInt i when reals -> (i |> ctx.MkReal) :> Z3.ArithExpr
        | AInt i -> (i |> ctx.MkInt) :> Z3.ArithExpr
        | AAdd xs -> ctx.MkAdd (xs |> Seq.map (arithToZ3 reals ctx) |> Seq.toArray)
        | ASub xs -> ctx.MkSub (xs |> Seq.map (arithToZ3 reals ctx) |> Seq.toArray)
        | AMul xs -> ctx.MkMul (xs |> Seq.map (arithToZ3 reals ctx) |> Seq.toArray)
        | ADiv (x, y) -> ctx.MkDiv (arithToZ3 reals ctx x, arithToZ3 reals ctx y)

    /// Converts a Starling Boolean expression to a Z3 ArithExpr.
    and boolToZ3 reals (ctx : Z3.Context) =
        function
        | BConst c -> c |> constToString |> ctx.MkBoolConst
        | BTrue -> ctx.MkTrue ()
        | BFalse -> ctx.MkFalse ()
        | BAnd xs -> ctx.MkAnd (xs |> Seq.map (boolToZ3 reals ctx) |> Seq.toArray)
        | BOr xs -> ctx.MkOr (xs |> Seq.map (boolToZ3 reals ctx) |> Seq.toArray)
        | BImplies (x, y) -> ctx.MkImplies (boolToZ3 reals ctx x, boolToZ3 reals ctx y)
        | BEq (x, y) -> ctx.MkEq (exprToZ3 reals ctx x, exprToZ3 reals ctx y)
        | BGt (x, y) -> ctx.MkGt (arithToZ3 reals ctx x, arithToZ3 reals ctx y)
        | BGe (x, y) -> ctx.MkGe (arithToZ3 reals ctx x, arithToZ3 reals ctx y)
        | BLe (x, y) -> ctx.MkLe (arithToZ3 reals ctx x, arithToZ3 reals ctx y)
        | BLt (x, y) -> ctx.MkLt (arithToZ3 reals ctx x, arithToZ3 reals ctx y)
        | BNot x -> x |> boolToZ3 reals ctx |> ctx.MkNot

    /// Converts a Starling expression to a Z3 Expr.
    and exprToZ3 reals (ctx: Z3.Context) =
        function
        | BExpr b -> boolToZ3 reals ctx b :> Z3.Expr
        | AExpr a -> arithToZ3 reals ctx a :> Z3.Expr

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
