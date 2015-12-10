module Starling.Tests.Modeller

open Chessie.ErrorHandling  // ok
open Fuchu                  // general test framework
open Microsoft.Z3           // anything involving ctx


open Starling
open Starling.Collections
open Starling.Var
open Starling.AST
open Starling.Model
open Starling.Modeller
open Starling.Tests.Studies

/// Assertion that converting the arithmetic expression `expr` to Z3
/// yields the given AST.
let assertZ3ArithExpr ctx expr z3 =
    let model = ticketLockModel ctx
    Assert.Equal (Starling.Pretty.AST.printExpression expr
                   + " -Z3-> " + z3.ToString (),
                  ok z3,
                  arithExprToZ3 model model.Locals expr)

/// Assertion that converting the Boolean expression `expr` to Z3
/// yields the given AST.
let assertZ3BoolExpr ctx expr z3 =
    let model = ticketLockModel ctx
    Assert.Equal (Starling.Pretty.AST.printExpression expr
                   + " -Z3-> " + z3.ToString (),
                  ok z3,
                  boolExprToZ3 model model.Locals expr)

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
                    (* We simplify obviously-true/false expressions down.
                     * This is one of them.
                     *)
                    assertZ3BoolExpr ctx
                                     (BopExp (And,
                                              BopExp (Or,
                                                      TrueExp,
                                                      TrueExp),
                                              FalseExp))
                                     (ctx.MkFalse ()) ] ]

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
let modelToComparable model =
    (model.Globals, model.Locals, model.Axioms, model.VProtos, model.DefViews)

let testModelPrimOnAtomic (ctx: Context) =
    testCase "test modelPrimOnAtomic with ticketed lock example" <|
        fun _ -> Assert.Equal ("modelPrimOnAtomic with <t = ticket++>",
                               ok (IntLoad (Some (LVIdent "t"),
                                           LVIdent "ticket",
                                           Increment)),
                               (modelPrimOnAtomic (ticketLockModel ctx)
                                                  (Fetch (LVIdent "t",
                                                          LVExp (LVIdent "ticket"),
                                                          Increment))))

let testModelAxiomOnCommand (ctx: Context) =
    testCase "test modelAxiomOnCommand with ticketed lock example" <|
        fun _ ->
            Assert.Equal
                ("modelAxiomOnCommand with {emp} <t = ticket++> {holdLock()}",
                 ok (PAAxiom {Conditions = {Pre = Multiset.empty ()
                                            Post = Multiset.ofList [CSetView {VName = "holdTick";
                                                                              VParams = [ctx.MkIntConst "t"]} ] }
                              Inner = IntLoad (Some (LVIdent "t"),
                                              LVIdent "ticket",
                                              Increment) } ),
                 (modelAxiomOnCommand (ticketLockModel ctx)
                                      {Pre = Multiset.empty ()
                                       Post = Multiset.ofList [CSetView {VName = "holdTick"
                                                                         VParams = [ctx.MkIntConst "t"]} ] }

                                      (Atomic (Fetch (LVIdent "t",
                                                      LVExp (LVIdent "ticket"),
                                                      Increment)))))

let testMakeAxiomConditionPair (ctx: Context) =
    testCase "Test makeAxiomConditionPair with ticketed lock example" <|
        fun _ -> Assert.Equal ("makeAxiomConditionPair emp holdTick(t)",
                               ok ( {Pre = Multiset.empty ()
                                     Post = Multiset.ofList [CSetView {VName = "holdTick"
                                                                       VParams = [ctx.MkIntConst "t"] } ] } ),
                               makeAxiomConditionPair (ticketLockModel ctx)
                                                      (Unit)
                                                      (Func ("holdTick", [LVExp (LVIdent "t") ] )))


let testTicketedLock ctx =
    testCase "Test that the ticketed lock produces the correct model" <|
    fun _ ->
        Assert.Equal
            ("ticketed lock collation -> ticketed lock model",
             ticketLockModel ctx |> ok |> lift modelToComparable,
             modelWith ctx ticketLockCollated |> lift modelToComparable)

[<Tests>]
let testModeller =
    let ctx = new Context ()
    let t = testList "Test the modeller"
                     [ testExprToZ3 ctx
                       testModelVars ctx
                       testModelPrimOnAtomic ctx
                       testMakeAxiomConditionPair ctx
                       testList "Test modelling of case studies"
                                [ testTicketedLock ctx ]]
    ctx.Dispose ()
    t
