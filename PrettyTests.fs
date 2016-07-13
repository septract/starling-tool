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
        [ TestCaseData(fresh_node <| Int 5L).Returns("5")
          TestCaseData(fresh_node <| Bop(Div, fresh_node <| Int 6L, fresh_node <| LV(LVIdent "bar"))).Returns("(6 / bar)")

          TestCaseData(fresh_node <| Bop(Mul, fresh_node <| Bop(Add, fresh_node <| Int 1L, fresh_node <| Int 2L), fresh_node <| Int 3L)).Returns("((1 + 2) * 3)") ]
        |> List.map (fun d -> d.SetName(sprintf "Print expression %A" d.ExpectedResult))

    [<TestCaseSource("Exprs")>]
    /// Tests whether printExpression behaves itself.
    member x.``printExpressions correctly prints expressions`` expr =
        expr
        |> printExpression
        |> Core.Pretty.print
