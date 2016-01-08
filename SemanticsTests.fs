module Starling.Tests.Semantics

open NUnit.Framework
open Starling
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Semantics
open Starling.Lang.AST
open Starling.Tests.Studies

/// Tests for the semantic transformer.
type SemanticsTests() =
    // Test cases for the expression framer.
    static member FrameExprs =
        [
            (
                new TestCaseData(
                    BTrue 
                )
            ).Returns(
               [ BEq(AExpr (AConst (After "serving")), AExpr (AConst (Before "serving")))
                 BEq(AExpr (AConst (After "ticket")), AExpr (AConst (Before "ticket")))
                 BEq(AExpr (AConst (After "s")), AExpr (AConst (Before "s")))
                 BEq(AExpr (AConst (After "t")), AExpr (AConst (Before "t"))) ]
            ).SetName("Frame id using the ticketed lock model")
            (
                new TestCaseData(
                    BAnd [ BGt(AConst (After "ticket"), AConst (Before "ticket"))
                           BLe(AConst (After "serving"), AConst (Before "serving"))
                           BConst (Unmarked "frozzle")
                           BEq(AExpr (AConst (Before "s")), AExpr (AConst (Before "t"))) ]
                )
            ).Returns(
               [ BEq(AExpr (AConst (After "s")), AExpr (AConst (Before "s")))
                 BEq(AExpr (AConst (After "t")), AExpr (AConst (Before "t"))) ]
            ).SetName("Frame a simple command expression using the ticketed lock model")
        ]

    // Test framing of expressions.
    [<TestCaseSource("FrameExprs")>]
    member x.``Test framing of expressions using the ticketed lock model`` expr =
        frame ticketLockModel expr

    /// Test cases for full command semantic translation.
    static member Commands =
        // Annoyingly, order of terms seems to matter here.
        // TODO(CaptainHayashi): weaken this test?
        [
            (
                new TestCaseData (
                    PrimAssume(BEq(AExpr (AConst (Unmarked "s")), AExpr (AConst (Unmarked "t"))))
                )
            ).Returns(
                BAnd [ BEq(AExpr (AConst (After "serving")), AExpr (AConst (Before "serving")))
                       BEq(AExpr (AConst (After "ticket")), AExpr (AConst (Before "ticket")))
                       BEq(AExpr (AConst (After "s")), AExpr (AConst (Before "s")))
                       BEq(AExpr (AConst (After "t")), AExpr (AConst (Before "t")))
                       BEq(AExpr (AConst (Before "s")), AExpr (AConst (Before "t"))) ] 
            ).SetName("semanticsOf with assume(s == t) and ticketed lock model")
            (
                new TestCaseData (
                   IntLoad(None, LVIdent "serving", Increment)
                )
            ).Returns(
               BAnd [ BEq(AExpr (AConst (After "ticket")), AExpr (AConst (Before "ticket")))
                      BEq(AExpr (AConst (After "s")), AExpr (AConst (Before "s")))
                      BEq(AExpr (AConst (After "t")), AExpr (AConst (Before "t")))
                      BEq(AExpr (AConst (After "serving")), 
                          AExpr (AAdd [ AConst (Before "serving")
                                        AInt 1L ])) ] 
            ).SetName("semanticsOf with serving++ and ticketed lock model")
        ]

    // Test semantic reification of commands.
    [<TestCaseSource("Commands")>]
    member x.``Test semantic translation of commands using the ticketed lock model`` com =
        semanticsOf ticketLockModel com
