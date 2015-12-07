module Starling.Tests.Semantics

open Fuchu
open Microsoft.Z3

open Starling.Var
open Starling.AST
open Starling.Model
open Starling.Semantics
open Starling.Tests.Studies

/// A nonsensical expression to test semantic rewrites.
let testExpr (ctx: Context) =
    ctx.MkAnd [|ctx.MkGt (ctx.MkIntConst "ticket!after",
                          ctx.MkIntConst "ticket!before")
                ctx.MkLe (ctx.MkIntConst "serving!after",
                          ctx.MkIntConst "serving!after")
                ctx.MkBoolConst "frozzle"
                ctx.MkEq (ctx.MkIntConst "s!before",
                          ctx.MkIntConst "t!before")|]

let testExprsInExpr ctx =
    testList "test exprsInExpr"
             [ testCase "exprsInExpr with no exprs" <|
               fun _ -> Assert.Equal ("exprsInExpr <> testExpr = <>",
                                      Set.empty,
                                      exprsInExpr Set.empty
                                                  (testExpr ctx))
               testCase "exprsInExpr with exprs" <|
               fun _ -> Assert.Equal ("exprsInExpr <serving!after ticket!after s!after> testExpr = <serving!after ticket!after>",
                                      new Set<Expr> ( [ ctx.MkIntConst "serving!after"
                                                        ctx.MkIntConst "ticket!after" ] ),
                                      exprsInExpr (Set<Expr> ( [ ctx.MkIntConst "serving!after"
                                                                 ctx.MkIntConst "ticket!after"
                                                                 ctx.MkIntConst "s!after" ] ))
                                                  (testExpr ctx)) ]

let testAftersInModel (ctx: Context) =
    testList "test aftersInModel"
             [ testCase "afters in the ticketed lock" <|
               fun _ -> Assert.Equal ("afters in ticketed lock = s!after, t!after, serving!after, ticket!after",
                                      new Set<Expr> ( [ ctx.MkIntConst "s!after"
                                                        ctx.MkIntConst "t!after"
                                                        ctx.MkIntConst "serving!after"
                                                        ctx.MkIntConst "ticket!after" ] ),
                                      aftersInModel (ticketLockModel ctx)) ]

let testAftersInExpr (ctx: Context) =
    testList "test aftersInExpr"
             [ testCase "aftersInExpr with the test expr and ticketed lock model" <|
               fun _ -> Assert.Equal ("aftersInExpr testExpr = <serving!after ticket!after>",
                                      new Set<Expr> ( [ ctx.MkIntConst "serving!after"
                                                        ctx.MkIntConst "ticket!after" ] ),
                                      aftersInExpr (ticketLockModel ctx) (testExpr ctx)) ]

let testAftersNotInExpr (ctx: Context) =
    testList "test aftersNotInExpr"
             [ testCase "aftersNotInExpr with the test expr and ticketed lock model" <|
               fun _ -> Assert.Equal ("aftersNotInExpr testExpr = <s!after t!after>",
                                      new Set<Expr> ( [ ctx.MkIntConst "s!after"
                                                        ctx.MkIntConst "t!after" ] ),
                                      aftersNotInExpr (ticketLockModel ctx) (testExpr ctx)) ]

let testFrame (ctx: Context) =
    testList "test frame"
             [ testCase "frame with the test expr and ticketed lock model" <|
               fun _ -> Assert.Equal ("frame testExpr = <s!after=s!before, t!after=s!before>",
                                      [ ctx.MkEq (ctx.MkIntConst "s!after",
                                                  ctx.MkIntConst "s!before")
                                        ctx.MkEq (ctx.MkIntConst "t!after",
                                                  ctx.MkIntConst "t!before") ],
                                      frame (ticketLockModel ctx) (testExpr ctx) |> Seq.toList) ]

let testSemanticsOf (ctx: Context) =
    testList "test semanticsOf"
             [ testCase "semanticsOf with assume(s == t) and ticketed lock model" <|
               fun _ -> Assert.Equal ("semanticsOf assume(s==t) <s!before = t!before; n!after = n!before>",
                                      // Annoyingly, order of terms seems to matter here.
                                      // TODO(CaptainHayashi): weaken this test?
                                      ctx.MkAnd [|ctx.MkEq (ctx.MkIntConst "serving!after",
                                                            ctx.MkIntConst "serving!before")
                                                  ctx.MkEq (ctx.MkIntConst "ticket!after",
                                                            ctx.MkIntConst "ticket!before")
                                                  ctx.MkEq (ctx.MkIntConst "s!after",
                                                            ctx.MkIntConst "s!before")
                                                  ctx.MkEq (ctx.MkIntConst "t!after",
                                                            ctx.MkIntConst "t!before")
                                                  ctx.MkEq (ctx.MkIntConst "s!before",
                                                            ctx.MkIntConst "t!before") |],
                                      semanticsOf (ticketLockModel ctx)
                                                  (PrimAssume (ctx.MkEq (ctx.MkIntConst "s",
                                                                         ctx.MkIntConst "t"))))
               testCase "semanticsOf with serving++ and ticketed lock model" <|
               fun _ -> Assert.Equal ("semanticsOf serving++ = <serving!after = serving!before + 1; n!after = n!before>",
                                      // Annoyingly, order of terms seems to matter here.
                                      // TODO(CaptainHayashi): weaken this test?
                                      ctx.MkAnd [|ctx.MkEq (ctx.MkIntConst "ticket!after",
                                                            ctx.MkIntConst "ticket!before")
                                                  ctx.MkEq (ctx.MkIntConst "s!after",
                                                            ctx.MkIntConst "s!before")
                                                  ctx.MkEq (ctx.MkIntConst "t!after",
                                                            ctx.MkIntConst "t!before")
                                                  ctx.MkEq (ctx.MkIntConst "serving!after",
                                                            ctx.MkAdd [|ctx.MkIntConst "serving!before" :> ArithExpr
                                                                        ctx.MkInt 1 :> ArithExpr|] ) |],
                                      semanticsOf (ticketLockModel ctx)
                                                  (IntLoad (None,
                                                            LVIdent "serving",
                                                            Increment))) ]

[<Tests>]
let testSemantics =
    let ctx = new Context ()
    let t = testList "Test the command semantics translation"
                     [testExprsInExpr ctx
                      testAftersInModel ctx
                      testAftersInExpr ctx
                      testAftersNotInExpr ctx
                      testFrame ctx
                      testSemanticsOf ctx]
    ctx.Dispose ()
    t
