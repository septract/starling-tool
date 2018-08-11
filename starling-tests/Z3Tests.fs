/// <summary>
///     Z3 tests for expressions.
/// </summary>
module Starling.Tests.Core.Z3

open NUnit.Framework

open Microsoft

open Starling.Tests.TestUtils

open Starling.Core.Expr
open Starling.Core.Z3

[<Test>]
let ``modulo expressions are translated correctly when reals is disabled`` () =
    use ctx = new Z3.Context ()
    assertEqual
        (ctx.MkMod (ctx.MkIntConst "foo", ctx.MkInt 5L) :> Z3.ArithExpr)
        (Expr.intToZ3 false id ctx (normalInt (mkMod (IVar "foo") (IInt 5L))))
