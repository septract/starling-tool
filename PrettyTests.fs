namespace Starling.Tests

open Fuchu
open Starling
open Starling.AST

module Pretty =
    [<Tests>]
    let testPretty =
        testList "Test the pretty-printer" [
            testList "Test pretty-printing of expressions" [
                testCase "pretty-print ((1 + 2) * 3)" <|
                    fun _ -> Assert.Equal ( "((1 + 2) * 3)"
                                          , "((1 + 2) * 3)"
                                          , Pretty.printExpression ( MulExp ( AddExp ( IntExp 1L
                                                                                     , IntExp 2L
                                                                                     )
                                                                            , IntExp 3L
                                                                            )
                                                                   )
                                          )
            ]
        ]