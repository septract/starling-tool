namespace Starling.Tests

open Fuchu
open FParsec
open Starling

module Parser =
    /// Assertion that parsing `concrete` with parser `pp` gets the AST `ast`.
    let assertParse pp msg concrete ast =
        Assert.Equal ( msg
                     , Some ast
                     , match ( run pp concrete ) with
                           | Success ( result, _, _ ) -> Some result
                           | Failure _                -> None
                     )

    /// Assertion that parsing expression `expr` with parser `pp` gets the AST `ast`.
    let assertParseExpr expr ast =
        assertParse Parser.parseExpression
                    ( expr + " -> " + Pretty.printExpression ast )
                    expr
                    ast

    let testExpressionPrecedence =
        testList "Test that parsing expressions yields correct precedence" [
            testCase "1 + 2 * 3 -> 1 + (2 * 3)" <|
                fun _ -> assertParseExpr "1 + 2 * 3"
                                         ( AddExp ( IntExp 1L, MulExp ( IntExp 2L, IntExp 3L ) ) )
            testCase "(1 + 2) * 3 -> (1 + 2) * 3" <|
                fun _ -> assertParseExpr "(1 + 2) * 3"
                                         ( MulExp ( AddExp ( IntExp 1L, IntExp 2L ), IntExp 3L ) )
            testCase "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8 -> ((1 + 2) < (3 * 4) && true) || ((5 / 6) > (7 - 8))" <|
                fun _ -> assertParseExpr "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8"
                                         ( OrExp ( AndExp ( LtExp ( AddExp ( IntExp 1L, IntExp 2L )
                                                                  , MulExp ( IntExp 3L, IntExp 4L )
                                                                  )
                                                          , TrueExp
                                                          )
                                                 , GtExp ( DivExp ( IntExp 5L, IntExp 6L )
                                                         , SubExp ( IntExp 7L, IntExp 8L )
                                                         )
                                                 )
                                         )
        ]

    let testAtomicFetch =
        testList "Test that atomic fetch actions are correctly parsed"
                 [ testCase "foo++" <|
                       fun _ -> assertParse Parser.parseAtomic
                                            "foo++"
                                            "foo++"
                                            ( Postfix ( "foo", Increment ) )
                   testCase "foo--" <|
                       fun _ -> assertParse Parser.parseAtomic
                                            "foo--"
                                            "foo--"
                                            ( Postfix ( "foo", Decrement ) )
                   testCase "foo = bar" <|
                       fun _ -> assertParse Parser.parseAtomic
                                            "foo = bar"
                                            "foo = bar"
                                            ( Fetch ( "foo", "bar", Direct ) )
                   testCase "foo = bar++" <|
                       fun _ -> assertParse Parser.parseAtomic
                                            "foo = bar++"
                                            "foo = bar++"
                                            ( Fetch ( "foo", "bar", Increment ) )
                   testCase "foo = bar--" <|
                       fun _ -> assertParse Parser.parseAtomic
                                            "foo = bar--"
                                            "foo = bar--"
                                            ( Fetch ( "foo", "bar", Decrement ) )
                   testCase "CAS(foo, 1, 2)" <|
                       fun _ -> assertParse Parser.parseAtomic
                                            "CAS(foo, 1, 2)"
                                            "CAS(foo, 1, 2)"
                                            ( CompareAndSwap ( "foo", IntExp 1L, IntExp 2L ) )
                 ]

    [<Tests>]
    let testParser =
        testList "Test the parser" [
            testList "Test parsing of expressions" [
                testExpressionPrecedence
            ]
            testList "Test parsing of atomics" [
                testAtomicFetch
            ]
        ]