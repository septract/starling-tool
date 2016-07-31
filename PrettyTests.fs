/// <summary>
///     Test module for the pretty printer module.
/// </summary>
module Starling.Tests.Pretty

open NUnit.Framework
open Starling
open Starling.Core.Var
open Starling.Lang.AST
open Starling.Lang.AST.Pretty

/// Tests for the pretty printer.
type PrettyTests() =

    /// Test cases for printExpression.
    static member Exprs =
        [ TestCaseData(freshNode <| Num 5L).Returns("5")
          TestCaseData(freshNode <| BopExpr(Div, freshNode <| Num 6L, freshNode <| LV(LVIdent "bar"))).Returns("(6 / bar)")

          TestCaseData(freshNode <| BopExpr(Mul, freshNode <| BopExpr(Add, freshNode <| Num 1L, freshNode <| Num 2L), freshNode <| Num 3L)).Returns("((1 + 2) * 3)") ]
        |> List.map (fun d -> d.SetName(sprintf "Print expression %A" d.ExpectedResult))

    [<TestCaseSource("Exprs")>]
    /// Tests whether printExpression behaves itself.
    member x.``printExpression correctly prints expressions`` expr =
        expr
        |> printExpression
        |> Core.Pretty.printUnstyled
