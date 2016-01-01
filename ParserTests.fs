module Starling.Tests.Lang.Parser

open NUnit.Framework
open FParsec
open Starling
open Starling.Var
open Starling.Lang.AST
open Starling.Lang.Parser
open Starling.Pretty.Lang.AST
open Starling.Pretty.Types

/// Tests for the parser.
type ParserTests() = 
    
    /// Helper method for building parser tests.
    /// Adapts to Some/None.
    static member ParseResultToOptional a = 
        match a with
        | Success(result, _, _) -> Some result
        | Failure _ -> None
    
    /// Test cases for testing the expression parser.
    static member ExpressionParses = 
        seq { 
            yield (new TestCaseData("1 + 2 * 3"))
                .Returns(Some(Bop(Add, Int 1L, Bop(Mul, Int 2L, Int 3L))))
            yield (new TestCaseData("(1 + 2) * 3"))
                .Returns(Some(Bop(Mul, Bop(Add, Int 1L, Int 2L), Int 3L)))
            yield (new TestCaseData("1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8"))
                .Returns(Some
                             ((Bop
                                   (Or, 
                                    Bop
                                        (And, 
                                         Bop
                                             (Lt, Bop(Add, Int 1L, Int 2L), Bop(Mul, Int 3L, Int 4L)), 
                                         True), 
                                    Bop(Gt, Bop(Div, Int 5L, Int 6L), Bop(Sub, Int 7L, Int 8L))))))
        }
    
    [<TestCaseSource("ExpressionParses")>]
    /// Tests whether the expression parser works correctly.
    member x.``the expression parser parses test case expressions correctly`` expr = 
        expr
        |> run parseExpression
        |> ParserTests.ParseResultToOptional
    
    /// Test cases for testing the atomic parser.
    static member AtomicParses = 
        seq { 
            yield (new TestCaseData("foo++")).Returns(Some(Postfix(LVIdent "foo", Increment)))
            yield (new TestCaseData("foo--")).Returns(Some(Postfix(LVIdent "foo", Decrement)))
            yield (new TestCaseData("foo = bar")).Returns(Some(Fetch(LVIdent "foo", LV(LVIdent "bar"), Direct)))
            yield (new TestCaseData("foo = bar++")).Returns(Some(Fetch(LVIdent "foo", LV(LVIdent "bar"), Increment)))
            yield (new TestCaseData("foo = bar--")).Returns(Some(Fetch(LVIdent "foo", LV(LVIdent "bar"), Decrement)))
            yield (new TestCaseData("CAS(foo, bar, 2)"))
                .Returns(Some(CompareAndSwap(LVIdent "foo", LVIdent "bar", Int 2L)))
        }
    
    [<TestCaseSource("AtomicParses")>]
    /// Tests whether the expression parser works correctly.
    member x.``the atomics parser parses test case atomics correctly`` expr = 
        expr
        |> run parseAtomic
        |> ParserTests.ParseResultToOptional
    
    /// Test cases for testing the full parser.
    static member ScriptParses = 
        seq 
            { 
            yield (new TestCaseData(Starling.Tests.Studies.ticketLock))
                .Returns(Some(Starling.Tests.Studies.ticketLockParsed)).SetName("parse the ticketed lock") }
    
    [<TestCaseSource("ScriptParses")>]
    /// Tests whether the script parser works correctly.
    member x.``the script parser parses full case studies correctly`` expr = 
        expr
        |> run parseScript
        |> ParserTests.ParseResultToOptional
