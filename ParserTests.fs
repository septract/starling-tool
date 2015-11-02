namespace Starling.Tests

open Fuchu
open FParsec
open Starling

module Parser =
    let testExpressionPrecedence =
        testList "Test that parsing expressions yields correct precedence" [
            testCase "1 + 2 * 3 <-> 1 + (2 * 3)" <|
                fun _ -> Assert.Equal ( "1 + 2 * 3 <-> 1 + (2 * 3)",
                                        Some ( AddExp ( IntExp 1L, MulExp ( IntExp 2L, IntExp 3L ) ) ),
                                        match ( run Parser.parseExpression "1 + 2 * 3" ) with
                                            | Success ( result, _, _ ) -> Some result
                                            | Failure _                -> None
                                      )
        ]

    [<Tests>]
    let testParser =
        testList "Test the parser" [
            testList "Test parsing of expressions" [
                testExpressionPrecedence
            ]
        ]