module Starling.Tests.Lang.Parser

open Fuchu
open FParsec
open Starling
open Starling.Var
open Starling.Lang.AST
open Starling.Lang.Parser
open Starling.Pretty.Lang.AST
open Starling.Pretty.Types

/// Assertion that parsing `concrete` with parser `pp` gets the AST `ast`.
let assertParse pp msg concrete ast = 
    Assert.Equal(msg, Some ast, 
                 match (run pp concrete) with
                 | Success(result, _, _) -> Some result
                 | Failure _ -> None)

/// Assertion that parsing expression `expr` with parser `pp` gets the AST `ast`.
let assertParseExpr expr ast = assertParse parseExpression (expr + " -> " + (ast |> printExpression |> print)) expr ast

(*
let testLValueIndirection =
    testList "Test that LValue indirection syntax works" [
        testCase "'foo' -> 0 indirections" <|
            fun _ -> assertParse Parser.parseLValue
                                 "'foo' -> 0 indirections"
                                 "foo"
                                 (LVIdent "foo")
        testCase "'*foo' -> 1 indirection" <|
            fun _ -> assertParse Parser.parseLValue
                                 "'*foo' -> 1 indirection"
                                 "*foo"
                                 (LVPtr (LVIdent "foo"))
        testCase "'**foo' -> 2 indirections" <|
            fun _ -> assertParse Parser.parseLValue
                                 "'**foo' -> 2 indirections"
                                 "**foo"
                                 (LVPtr (LVPtr (LVIdent "foo"))) ]
*)

let testExpressionPrecedence = 
    testList "Test that parsing expressions yields correct precedence" 
        [ testCase "1 + 2 * 3 -> 1 + (2 * 3)" 
          <| fun _ -> assertParseExpr "1 + 2 * 3" (BopExp(Add, IntExp 1L, BopExp(Mul, IntExp 2L, IntExp 3L)))
          
          testCase "(1 + 2) * 3 -> (1 + 2) * 3" 
          <| fun _ -> assertParseExpr "(1 + 2) * 3" (BopExp(Mul, BopExp(Add, IntExp 1L, IntExp 2L), IntExp 3L))
          
          testCase "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8 - > ((1 +  2) < (3 * 4) && true) || ((5 / 6) > (7 - 8))" 
          <| fun _ -> 
              assertParseExpr "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8" 
                  (BopExp
                       (Or, 
                        BopExp
                            (And, BopExp(Lt, BopExp(Add, IntExp 1L, IntExp 2L), BopExp(Mul, IntExp 3L, IntExp 4L)), 
                             TrueExp), BopExp(Gt, BopExp(Div, IntExp 5L, IntExp 6L), BopExp(Sub, IntExp 7L, IntExp 8L)))) ]

let testAtomicFetch = 
    testList "Test that atomic fetch actions are correctly parsed" 
        [ testCase "foo++" <| fun _ -> assertParse parseAtomic "foo++" "foo++" (Postfix(LVIdent "foo", Increment))
          testCase "foo--" <| fun _ -> assertParse parseAtomic "foo--" "foo--" (Postfix(LVIdent "foo", Decrement))
          
          testCase "foo = bar" 
          <| fun _ -> 
              assertParse parseAtomic "foo = bar" "foo = bar" (Fetch(LVIdent "foo", LVExp(LVIdent "bar"), Direct))
          
          testCase "foo = bar++" 
          <| fun _ -> 
              assertParse parseAtomic "foo = bar++" "foo = bar++" 
                  (Fetch(LVIdent "foo", LVExp(LVIdent "bar"), Increment))
          
          testCase "foo = bar--" 
          <| fun _ -> 
              assertParse parseAtomic "foo = bar--" "foo = bar--" 
                  (Fetch(LVIdent "foo", LVExp(LVIdent "bar"), Decrement))
          
          testCase "CAS(foo, bar, 2)" 
          <| fun _ -> 
              assertParse parseAtomic "CAS(foo, bar, 2)" "CAS(foo, bar, 2)" 
                  (CompareAndSwap(LVIdent "foo", LVIdent "bar", IntExp 2L)) ]

let testTicketedLock = 
    testCase "Parse the ticketed lock" 
    <| fun _ -> 
        assertParse parseScript Starling.Tests.Studies.ticketLock Starling.Tests.Studies.ticketLock 
            Starling.Tests.Studies.ticketLockParsed

[<Tests>]
let testParser = 
    testList "Test the parser" [ //testList "Test parsing of lvalues" [
                                 //    testLValueIndirection ]
                                 testList "Test parsing of expressions" [ testExpressionPrecedence ]
                                 testList "Test parsing of atomics" [ testAtomicFetch ]
                                 testList "Test parsing of case studies" [ testTicketedLock ] ]
