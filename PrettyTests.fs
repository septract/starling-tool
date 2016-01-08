/// Test module for the pretty printer module.
module Starling.Tests.Pretty

open NUnit.Framework
open Starling
open Starling.Var
open Starling.Lang.AST
open Starling.Pretty.Lang.AST

/// Tests for the pretty printer.
type PrettyTests() = 
    
    /// Test cases for printExpression.
    static member Exprs = 
        [
            (new TestCaseData(Int 5L)).Returns("5").SetName("print expression 5")
            (new TestCaseData(Bop(Div, Int 6L, LV (LVIdent "bar")))).Returns("(6 / bar)").SetName("print expression 6 / bar")
            (new TestCaseData(Bop(Mul, Bop(Add, Int 1L, Int 2L), Int 3L))).Returns("((1 + 2) * 3)").SetName("print expression (1 + 2) * 3")
        ]
    
    [<TestCaseSource("Exprs")>]
    /// Tests whether printExpression behaves itself.
    member x.``printExpression correctly prints expressions`` expr = 
        expr
        |> printExpression
        |> Pretty.Types.print
