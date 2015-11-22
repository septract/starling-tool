module Starling.Tests.Modeller

open Chessie.ErrorHandling  // ok
open Fuchu                  // general test framework
open Microsoft.Z3           // anything involving ctx
open Starling
open Starling.AST

/// Assertion that converting the arithmetic expression `expr` to Z3
/// yields the given AST.
let assertZ3ArithExpr ctx expr z3 =
    Assert.Equal (Starling.Pretty.AST.printExpression expr
                   + " -Z3-> " + z3.ToString (),
                  Starling.Modeller.arithExprToZ3 ctx expr,
                  ok z3)

/// Assertion that converting the Boolean expression `expr` to Z3
/// yields the given AST.
let assertZ3BoolExpr ctx expr z3 =
    Assert.Equal (Starling.Pretty.AST.printExpression expr
                   + " -Z3-> " + z3.ToString (),
                  Starling.Modeller.boolExprToZ3 ctx expr,
                  ok z3)

let testExprToZ3 ctx =
    testList "Test translation of expressions" [
        testList "Test translation of arithmetic expressions" [
            testCase "Test arithmetic-only expressions" <|
                fun _ ->
                    assertZ3ArithExpr ctx
                                      (AddExp (MulExp (IntExp 1L,
                                                       IntExp 2L),
                                               IntExp 3L))
                                      (ctx.MkAdd [| ctx.MkMul [| ctx.MkInt 1 :> ArithExpr
                                                                 ctx.MkInt 2 :> ArithExpr |]
                                                    ctx.MkInt 3 :> ArithExpr |]) ]
        testList "Test translation of Boolean expressions" [
            testCase "Test Boolean-only expressions" <|
                fun _ ->
                    assertZ3BoolExpr ctx
                                     (AndExp (OrExp (TrueExp,
                                                     TrueExp),
                                             FalseExp))
                                     (ctx.MkAnd [| ctx.MkOr [| ctx.MkTrue ()
                                                               ctx.MkTrue () |]
                                                   ctx.MkFalse () |]) ]]

let testModelVarListNoDuplicates ctx =
    testList "Test modelling of variables forbids duplicates"
        [ testCase "Forbid duplicate with same type"
          <| fun _ -> Assert.Equal ("bool foo; bool foo -> error",
                                    fail <| Starling.Errors.Modeller.VEDuplicate "foo",
                                    Starling.Modeller.modelVarList ctx [ (Bool, "foo")
                                                                         (Bool, "foo") ])
          testCase "Forbid duplicate with different type"
          <| fun _ -> Assert.Equal ("bool foo; int foo -> error",
                                    fail <| Starling.Errors.Modeller.VEDuplicate "foo",
                                    Starling.Modeller.modelVarList ctx [ (Bool, "foo")
                                                                         (Int, "foo") ])
        ]

let testModelVars ctx =
    testList "Test modelling of variables"
        [ testModelVarListNoDuplicates ctx ]

        (*
let testTicketedLock =
    testCase "Test that the ticketed lock produces the correct model" <|
    fun _ ->
        Assert.Equal
            "ticketed lock collation -> ticketed lock model"
            {
            }
            (Starling.Modeller.model
            *)


[<Tests>]
let testModeller =
    let ctx = new Context ()
    let t = testList "Test the modeller"
                     [ testExprToZ3 ctx
                       testModelVars ctx
                       (*testTicketedLock*) ]
    ctx.Dispose ()
    t
