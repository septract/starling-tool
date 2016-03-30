module Starling.Tests.Lang.Parser

open NUnit.Framework
open FParsec
open Starling
open Starling.Core.Var
open Starling.Lang.AST
open Starling.Lang.Parser

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
        [ TestCaseData("1 + 2 * 3").Returns(Some(Bop(Add, Int 1L, Bop(Mul, Int 2L, Int 3L))))
          TestCaseData("(1 + 2) * 3").Returns(Some(Bop(Mul, Bop(Add, Int 1L, Int 2L), Int 3L)))

          TestCaseData("1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8")
              .Returns(Some
                           ((Bop
                                 (Or, Bop(And, Bop(Lt, Bop(Add, Int 1L, Int 2L), Bop(Mul, Int 3L, Int 4L)), True),
                                  Bop(Gt, Bop(Div, Int 5L, Int 6L), Bop(Sub, Int 7L, Int 8L)))))) ]
        |> List.map (fun d -> d.SetName(sprintf "Parse %A" d.OriginalArguments.[0]))

    [<TestCaseSource("ExpressionParses")>]
    /// Tests whether the expression parser works correctly.
    member x.``the expression parser parses test case expressions correctly`` expr =
        expr
        |> run parseExpression
        |> ParserTests.ParseResultToOptional

    /// Test cases for testing the atomics parser.
    static member AtomicParses =
        [ TestCaseData("foo++").Returns(Some(Postfix(LVIdent "foo", Increment)))
          TestCaseData("foo--").Returns(Some(Postfix(LVIdent "foo", Decrement)))
          TestCaseData("foo = bar").Returns(Some(Fetch(LVIdent "foo", LV(LVIdent "bar"), Direct)))
          TestCaseData("foo = bar++").Returns(Some(Fetch(LVIdent "foo", LV(LVIdent "bar"), Increment)))
          TestCaseData("foo = bar--").Returns(Some(Fetch(LVIdent "foo", LV(LVIdent "bar"), Decrement)))
          TestCaseData("CAS(foo, bar, 2)").Returns(Some(CompareAndSwap(LVIdent "foo", LVIdent "bar", Int 2L))) ]
        |> List.map (fun d -> d.SetName(sprintf "Parse %A" d.OriginalArguments.[0]))

    [<TestCaseSource("AtomicParses")>]
    /// Tests whether the atomics parser works correctly.
    member x.``the atomics parser parses test case prims correctly`` expr =
        expr
        |> run parseAtomic
        |> ParserTests.ParseResultToOptional


    /// Test cases for testing the atomic collection parser.
    static member AtomicSetParses =
        [ TestCaseData("<foo++>")
            .Returns(Some[ Postfix(LVIdent "foo", Increment) ])
            .SetName("Parse one atomic in angle brackets correctly")
          TestCaseData("<foo++; bar-->")
            .Returns(None)
            .SetName("Refuse more than one atomic outside a block")
          TestCaseData("< { foo++; } >")
            .Returns(Some [ Postfix(LVIdent "foo", Increment) ])
            .SetName("Parse one atomic in an atomic block correctly")
          TestCaseData("< { foo++; bar--; } >")
            .Returns(Some [ Postfix(LVIdent "foo", Increment)
                            Postfix(LVIdent "bar", Decrement) ])
            .SetName("Parse two atomic in an atomic block correctly") ]

    [<TestCaseSource("AtomicSetParses")>]
    /// Tests whether the atomic set parser works correctly.
    member x.``the atomic set parser parses sets correctly`` expr =
        expr
        |> run parseAtomicSet
        |> ParserTests.ParseResultToOptional


    /// Test cases for testing the constraint parser.
    static member ConstraintParses =
        [ TestCaseData("constraint emp -> true;").Returns(Some { CView = ViewDef.Unit
                                                                 CExpression = Some True })

          TestCaseData("constraint Func(a, b) -> c > a + b;")
              .Returns(Some { CView =
                                  ViewDef.Func { Name = "Func"
                                                 Params = [ "a"; "b" ] }
                              CExpression = Some <| Bop(Gt, LV(LVIdent "c"), Bop(Add, LV(LVIdent "a"), LV(LVIdent "b"))) })

          TestCaseData("constraint Func(a, b) -> ?;")
              .Returns(Some { CView =
                                  ViewDef.Func { Name = "Func"
                                                 Params = [ "a"; "b" ] }
                              CExpression = None }) ]
        |> List.map (fun d -> d.SetName(sprintf "Parse %A" d.OriginalArguments.[0]))

    [<TestCaseSource("ConstraintParses")>]
    /// Tests whether the constraint parser works correctly.
    member x.``the constraint parser parses valid constraints correctly`` cs =
        cs
        |> run parseConstraint
        |> ParserTests.ParseResultToOptional

    /// Test cases for testing the full parser.
    static member ScriptParses =
        [ TestCaseData(Starling.Tests.Studies.ticketLock).Returns(Some(Starling.Tests.Studies.ticketLockParsed))
            .SetName("Parse the ticket lock") ]

    [<TestCaseSource("ScriptParses")>]
    /// Tests whether the script parser works correctly.
    member x.``the script parser parses full case studies correctly`` expr =
        expr
        |> run parseScript
        |> ParserTests.ParseResultToOptional
