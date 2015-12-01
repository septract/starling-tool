module Starling.Tests.Modeller

open Chessie.ErrorHandling  // ok
open Fuchu                  // general test framework
open Microsoft.Z3           // anything involving ctx
open Starling
open Starling.Var
open Starling.AST
open Starling.Model
open Starling.Tests.Studies

/// Assertion that converting the arithmetic expression `expr` to Z3
/// yields the given AST.
let assertZ3ArithExpr ctx expr z3 =
    let model = ticketLockModel ctx
    Assert.Equal (Starling.Pretty.AST.printExpression expr
                   + " -Z3-> " + z3.ToString (),
                  Starling.Modeller.arithExprToZ3 model model.AllVars expr,
                  ok z3)

/// Assertion that converting the Boolean expression `expr` to Z3
/// yields the given AST.
let assertZ3BoolExpr ctx expr z3 =
    let model = ticketLockModel ctx
    Assert.Equal (Starling.Pretty.AST.printExpression expr
                   + " -Z3-> " + z3.ToString (),
                  Starling.Modeller.boolExprToZ3 model model.AllVars expr,
                  ok z3)

let testExprToZ3 ctx =
    testList "Test translation of expressions" [
        testList "Test translation of arithmetic expressions" [
            testCase "Test arithmetic-only expressions" <|
                fun _ ->
                    assertZ3ArithExpr ctx
                                      (BopExp (Add,
                                               BopExp (Mul,
                                                       IntExp 1L,
                                                       IntExp 2L),
                                               IntExp 3L))
                                      (ctx.MkAdd [| ctx.MkMul [| ctx.MkInt 1 :> ArithExpr
                                                                 ctx.MkInt 2 :> ArithExpr |]
                                                    ctx.MkInt 3 :> ArithExpr |]) ]
        testList "Test translation of Boolean expressions" [
            testCase "Test Boolean-only expressions" <|
                fun _ ->
                    assertZ3BoolExpr ctx
                                     (BopExp (And,
                                              BopExp (Or,
                                                      TrueExp,
                                                      TrueExp),
                                              FalseExp))
                                     (ctx.MkAnd [| ctx.MkOr [| ctx.MkTrue ()
                                                               ctx.MkTrue () |]
                                                   ctx.MkFalse () |]) ]]

let testModelVarListNoDuplicates ctx =
    testList "Test modelling of variables forbids duplicates"
        [ testCase "Forbid duplicate with same type"
          <| fun _ -> Assert.Equal ("bool foo; bool foo -> error",
                                    fail <| Starling.Errors.Var.VMEDuplicate "foo",
                                    Starling.Var.makeVarMap ctx [ (Bool, "foo")
                                                                  (Bool, "foo") ])
          testCase "Forbid duplicate with different type"
          <| fun _ -> Assert.Equal ("bool foo; int foo -> error",
                                    fail <| Starling.Errors.Var.VMEDuplicate "foo",
                                    Starling.Var.makeVarMap ctx [ (Bool, "foo")
                                                                  (Int, "foo") ])
        ]

let testModelVars ctx =
    testList "Test modelling of variables"
        [ testModelVarListNoDuplicates ctx ]

/// Converts a model to some form that is accurately comparable.
let modelToComparable =
    // TODO(CaptainHayashi): this is pretty drastic...
    Starling.Pretty.Misc.printPartModel >> Starling.Pretty.Types.print
    

let testTicketedLock ctx =
    testCase "Test that the ticketed lock produces the correct model" <|
    fun _ ->
        Assert.Equal
            ("ticketed lock collation -> ticketed lock model",
             ticketLockModel ctx |> ok |> lift modelToComparable,
             Starling.Modeller.modelWith ctx ticketLockCollated |> lift modelToComparable)

[<Tests>]
let testModeller =
    let ctx = new Context ()
    let t = testList "Test the modeller"
                     [ testExprToZ3 ctx
                       testModelVars ctx
                       testList "Test modelling of case studies"
                                [ testTicketedLock ctx ]]
    ctx.Dispose ()
    t
