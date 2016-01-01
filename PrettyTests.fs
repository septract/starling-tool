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
        seq { 
            yield (new TestCaseData(IntExp 5L)).Returns("5").SetName("print expression 5")
            yield (new TestCaseData(BopExp(Div, IntExp 6L, LVExp (LVIdent "bar")))).Returns("(6 / bar)").SetName("print expression 6 / bar")
            yield (new TestCaseData(BopExp(Mul, BopExp(Add, IntExp 1L, IntExp 2L), IntExp 3L))).Returns("((1 + 2) * 3)").SetName("print expression (1 + 2) * 3")
        }
    
    [<TestCaseSource("Exprs")>]
    /// Tests whether printExpression behaves itself.
    member x.``printExpression correctly prints expressions`` expr = 
        expr
        |> printExpression
        |> Pretty.Types.print
