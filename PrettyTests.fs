module Starling.Tests.Pretty

open Fuchu
open Starling
open Starling.AST

[<Tests>]
let testPretty =
    testList "Test the pretty-printer"
             [ testList "Test pretty-printing of expressions"
                        [ testCase "pretty-print ((1 + 2) * 3)" <|
                          fun _ ->
                              Assert.Equal ("((1 + 2) * 3)",
                                            "((1 + 2) * 3)",
                                            Pretty.AST.printExpression (MulExp (AddExp (IntExp 1L,
                                                                                        IntExp 2L),
                                                                                IntExp 3L))) ]]
