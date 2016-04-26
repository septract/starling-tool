module Starling.Tests.Core.Expr

open NUnit.Framework
open Starling.Core.TypeSystem
open Starling.Core.Axiom
open Starling.Core.Var
open Starling.Core.Command
open Starling.Core.Command.Compose
open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Sub

open Starling.Core.Pretty
open Starling.Core.Expr.Pretty
open Starling.Core.Var.Pretty

let tcd : obj[] -> TestCaseData = TestCaseData

/// Tests for the expression types and functions.
type ExprTests() =
    /// Test cases for testing simple/compound arithmetic classification.
    static member IntSimpleCompound =
        [ TestCaseData(AInt 1L)
            .Returns(false)
            .SetName("Classify '1' as simple")
          TestCaseData(AAdd [AInt 1L; AInt 2L])
            .Returns(true)
            .SetName("Classify '1+2' as compound")
          TestCaseData(ASub [AAdd [AInt 1L; AInt 2L]; AInt 3L])
            .Returns(true)
            .SetName("Classify '(1+2)-3' as compound")
          TestCaseData(iBefore "foo")
            .Returns(false)
            .SetName("Classify 'foo!before' as simple")
          TestCaseData(AMul [iBefore "foo"; iAfter "bar"])
            .Returns(true)
            .SetName("Classify 'foo!before * bar!after' as compound") ]

    /// Tests whether the simple/compound arithmetic patterns work correctly
    [<TestCaseSource("IntSimpleCompound")>]
    member x.``SimpleInt and CompoundInt classify properly`` e =
        match e with
        | SimpleInt -> false
        | CompoundInt -> true


    /// Test cases for intermediate finding.
    static member NextIntermediates =
        [ TestCaseData(Expr.Bool (sbInter 5I "foo"))
            .Returns(6I)
            .SetName("nextIntermediate on Bool intermediate is one higher")
          TestCaseData(Expr.Bool (BNot (sbInter 10I "bar")))
            .Returns(11I)
            .SetName("nextIntermediate on 'not' passes through")
          TestCaseData(Expr.Bool (BImplies (sbInter 6I "a", sbInter 11I "b")))
            .Returns(12I)
            .SetName("nextIntermediate on 'implies' is one higher than max")
          TestCaseData(Expr.Int
                           (AAdd [ siInter 1I "a"
                                   siAfter "b"
                                   siBefore "c"
                                   siInter 2I "d" ] ))
            .Returns(3I)
            .SetName("nextIntermediate on 'add' is one higher than max") ]

    /// Tests whether nextIntermediate works.
    [<TestCaseSource("NextIntermediates")>]
    member x.``test whether nextIntermediate gets the correct level`` expr =
        nextIntermediate expr

    /// Test cases for testing goal rewriting.
    static member GoalConstants =
        [ TestCaseData( [ "foo"; "foo"; "foo"] )
              .Returns( [ Reg (Goal (0I, "foo"))
                          Reg (Goal (1I, "foo"))
                          Reg (Goal (2I, "foo")) ] )
          TestCaseData( ["foo"; "bar"; "baz"] )
              .Returns( [ Reg (Goal (0I, "foo"))
                          Reg (Goal (1I, "bar"))
                          Reg (Goal (2I, "baz")) ] ) ]

    /// Tests that the frame name generator works fine.
    [<TestCaseSource("GoalConstants")>]
    member x.``goal generation uses fresh variables properly`` xs =
        // TODO(CaptainHayashi): move this to AxiomTests.
        let fg = freshGen ()

        // The fun x boilerplate seems to be necessary.
        // Otherwise, mutations to fg apparently don't propagate!
        List.map (fun x -> goalVar fg x) xs

    /// Test cases for testing constant post-state rewriting.
    static member IntConstantPostStates =
        [ TestCaseData(siVar "target1")
              .Returns(siAfter "target1")
              .SetName("Rewrite single variable to post-state")
          TestCaseData(AAdd [AInt 4L; siVar "target1"])
              .Returns(AAdd [AInt 4L; siAfter "target1"])
              .SetName("Rewrite expression with one variable to post-state")
          TestCaseData(ASub [siVar "target1"; siVar "target2"])
              .Returns(ASub [siAfter "target1"; siAfter "target2"])
              .SetName("Rewrite expression with two variables to post-state")
          TestCaseData(ADiv (AInt 6L, AInt 0L) : SVIntExpr)
              .Returns(ADiv (AInt 6L, AInt 0L) : SMIntExpr)
              .SetName("Rewrite expression with no variables to post-state") ]

    [<TestCaseSource("IntConstantPostStates")>]
    /// Tests whether rewriting constants in arithmetic expressions to post-state works.
    member x.``constants in arithmetic expressions can be rewritten to post-state`` expr =
        Mapper.mapInt after expr

    /// Test cases for negation checking.
    static member ObviousNegations =
        [ (tcd [| (BTrue : VBoolExpr)
                  (BFalse : VBoolExpr) |])
            .Returns(true)
          (tcd [| (BTrue : VBoolExpr)
                  (BTrue : VBoolExpr) |])
            .Returns(false)
          (tcd [| (BFalse : VBoolExpr)
                  (BFalse : VBoolExpr) |])
            .Returns(false)
          (tcd [| (BTrue : VBoolExpr)
                  (iEq (AInt 5L) (AInt 6L) : VBoolExpr) |])
            .Returns(true)
          (tcd [| (iEq (AVar "x") (AInt 2L))
                  (BNot (iEq (AVar "x") (AInt 2L))) |])
            .Returns(true)
          (tcd [| (iEq (AVar "x") (AInt 2L))
                  (BNot (iEq (AVar "y") (AInt 2L))) |])
            .Returns(false)
          // De Morgan
          (tcd [| (BAnd [ BVar "x" ; BVar "y" ])
                  (BOr [ BNot (BVar "x")
                         BNot (BVar "y") ] ) |] )
            .Returns(true)
          (tcd [| (BAnd [ BVar "x" ; BVar "y" ])
                  (BOr [ BNot (BVar "y")
                         BNot (BVar "x") ] ) |] )
            .Returns(true)
          (tcd [| (BOr [ BVar "x" ; BVar "y" ])
                  (BAnd [ BNot (BVar "x")
                          BNot (BVar "y") ] ) |] )
            .Returns(true)
          (tcd [| (BOr [ BVar "x" ; BVar "y" ])
                  (BAnd [ BNot (BVar "y")
                          BNot (BVar "x") ] ) |] )
            .Returns(true) ]
        |> List.map (
            fun d -> d.SetName(sprintf "%s and %s are %s negation"
                                        (((d.OriginalArguments.[1])
                                          :?> VBoolExpr)
                                         |> printVBoolExpr |> print)
                                        (((d.OriginalArguments.[0])
                                          :?> VBoolExpr)
                                         |> printVBoolExpr |> print)
                                        (if (d.ExpectedResult :?> bool)
                                         then "a" else "not a")))

    /// Checks whether negation checking is sound and sufficiently complete.
    [<TestCaseSource("ObviousNegations")>]
    member x.``negates is sound and sufficiently complete`` a b =
        equivHolds id (negates a b)
