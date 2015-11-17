module Starling.Tests.Z3

open Chessie.ErrorHandling  // ok
open Fuchu                  // general test framework
open Microsoft.Z3           // anything involving ctx
open Starling
open Starling.AST

/// Assertion that converting the arithmetic expression `expr` to Z3
/// yields the given AST.
let assertZ3ArithExpr ctx expr z3 =
    Assert.Equal ( Starling.Pretty.printExpression expr
                   + " -Z3-> " + z3.ToString ()
                 , Starling.Z3.arithExprToZ3 ctx expr
                 , ok z3
                 )

/// Assertion that converting the Boolean expression `expr` to Z3
/// yields the given AST.
let assertZ3BoolExpr ctx expr z3 =
    Assert.Equal ( Starling.Pretty.printExpression expr
                   + " -Z3-> " + z3.ToString ()
                 , Starling.Z3.boolExprToZ3 ctx expr
                 , ok z3
                 )

let testExprToZ3 ctx =
    testList "Test translation of expressions" [
        testList "Test translation of arithmetic expressions" [
            testCase "Test arithmetic-only expressions" <|
                fun _ -> assertZ3ArithExpr ctx
                                    ( AddExp ( MulExp ( IntExp 1L
                                                    , IntExp 2L
                                                    )
                                            , IntExp 3L
                                            )
                                    )
                                    ( ctx.MkAdd [| ctx.MkMul [| ctx.MkInt 1 :> ArithExpr
                                                            ; ctx.MkInt 2 :> ArithExpr
                                                            |]
                                                ; ctx.MkInt 3 :> ArithExpr
                                                |]
                                    )
        ]
        testList "Test translation of Boolean expressions" [
            testCase "Test Boolean-only expressions" <|
                fun _ -> assertZ3BoolExpr ctx
                                    ( AndExp ( OrExp ( TrueExp
                                                    , TrueExp
                                                    )
                                            , FalseExp
                                            )
                                    )
                                    ( ctx.MkAnd [| ctx.MkOr [| ctx.MkTrue ()
                                                            ; ctx.MkTrue ()
                                                            |]
                                                ; ctx.MkFalse ()
                                                |])
        ]
    ]

let testModelVarListNoDuplicates ctx =
    testList "Test modelling of variables forbids duplicates"
        [ testCase "Forbid duplicate with same type"
          <| fun _ -> Assert.Equal ("bool foo; bool foo -> error",
                                    Starling.Z3.modelVarList ctx [ (Bool, "foo")
                                                                   (Bool, "foo") ],
                                    fail <| Starling.Z3.VEDuplicate "foo")
          testCase "Forbid duplicate with different type"
          <| fun _ -> Assert.Equal ("bool foo; int foo -> error",
                                    Starling.Z3.modelVarList ctx [ (Bool, "foo")
                                                                   (Int, "foo") ],
                                    fail <| Starling.Z3.VEDuplicate "foo")
        ]

let testModelVars ctx =
    testList "Test modelling of variables"
        [ testModelVarListNoDuplicates ctx ]

[<Tests>]
let testZ3 =
    let ctx = new Context ()
    let t = testList "Test the Z3 translation"
                     [ testExprToZ3 ctx
                       testModelVars ctx ]
    ctx.Dispose ()
    t
