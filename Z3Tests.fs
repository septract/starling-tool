namespace Starling.Tests

open Chessie.ErrorHandling  // ok
open Fuchu                  // general test framework
open Microsoft.Z3           // anything involving ctx
open Starling
open Starling.AST

module Z3 =
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

    let testExprToZ3 =
        let ctx = new Context ()
        let t =
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
        ctx.Dispose ()
        t

    [<Tests>]
    let testZ3 =
        testList "Test the Z3 translation" [
            testExprToZ3
        ]