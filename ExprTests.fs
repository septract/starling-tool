module Starling.Tests.Core.Expr

open NUnit.Framework
open Starling.Core.Axiom
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Sub

open Starling.Core.Pretty
open Starling.Core.Expr.Pretty

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
        [ TestCaseData(siUnmarked "target1")
              .Returns(siAfter "target1")
              .SetName("Rewrite single target constant to post-state")
          TestCaseData(siUnmarked "notTarget")
              .Returns(siUnmarked "notTarget")
              .SetName("Rewrite single non-target constant to post-state")
          TestCaseData(AAdd [AInt 4L; siUnmarked "target1"])
              .Returns(AAdd [AInt 4L; siAfter "target1"])
              .SetName("Rewrite expression with one target constant to post-state")
          TestCaseData(ASub [siUnmarked "target1"; siUnmarked "target2"])
              .Returns(ASub [siAfter "target1"; siAfter "target2"])
              .SetName("Rewrite expression with two target constants to post-state")
          TestCaseData(ADiv (AInt 6L, AInt 0L) : SMIntExpr)
              .Returns(ADiv (AInt 6L, AInt 0L) : SMIntExpr)
              .SetName("Rewrite expression with no constants to post-state")
          TestCaseData(AMul [siUnmarked "foo"; siUnmarked "bar"])
              .Returns(AMul [siUnmarked "foo"; siUnmarked "bar"])
              .SetName("Rewrite expression with two non-target constants to post-state") ]

    [<TestCaseSource("IntConstantPostStates")>]
    /// Tests whether rewriting constants in arithmetic expressions to post-state works.
    member x.``constants in arithmetic expressions can be rewritten to post-state`` expr =
        TypeMapper.mapInt
            (liftMarker After (Set.ofList ["target1"; "target2"] |> inSet))
            expr

    /// Test cases for negation checking.
    static member ObviousNegations =
        [ (tcd [| (BTrue : MBoolExpr)
                  (BFalse : MBoolExpr) |])
            .Returns(true)
          (tcd [| (BTrue : MBoolExpr)
                  (BTrue : MBoolExpr) |])
            .Returns(false)
          (tcd [| (BFalse : MBoolExpr)
                  (BFalse : MBoolExpr) |])
            .Returns(false)
          (tcd [| (BTrue : MBoolExpr)
                  (iEq (AInt 5L) (AInt 6L) : MBoolExpr) |])
            .Returns(true)
          (tcd [| (iEq (iUnmarked "x") (AInt 2L))
                  (BNot (iEq (iUnmarked "x") (AInt 2L))) |])
            .Returns(true)
          (tcd [| (iEq (iUnmarked "x") (AInt 2L))
                  (BNot (iEq (iUnmarked "y") (AInt 2L))) |])
            .Returns(false)
          // De Morgan
          (tcd [| (BAnd [ bUnmarked "x" ; bUnmarked "y" ])
                  (BOr [ BNot (bUnmarked "x")
                         BNot (bUnmarked "y") ] ) |] )
            .Returns(true)
          (tcd [| (BAnd [ bUnmarked "x" ; bUnmarked "y" ])
                  (BOr [ BNot (bUnmarked "y")
                         BNot (bUnmarked "x") ] ) |] )
            .Returns(true)
          (tcd [| (BOr [ bUnmarked "x" ; bUnmarked "y" ])
                  (BAnd [ BNot (bUnmarked "x")
                          BNot (bUnmarked "y") ] ) |] )
            .Returns(true)
          (tcd [| (BOr [ bUnmarked "x" ; bUnmarked "y" ])
                  (BAnd [ BNot (bUnmarked "y")
                          BNot (bUnmarked "x") ] ) |] )
            .Returns(true) ]
        |> List.map (
            fun d -> d.SetName(sprintf "%s and %s are %s negation"
                                        (((d.OriginalArguments.[1])
                                          :?> MBoolExpr)
                                         |> printMBoolExpr |> print)
                                        (((d.OriginalArguments.[0])
                                          :?> MBoolExpr)
                                         |> printMBoolExpr |> print)
                                        (if (d.ExpectedResult :?> bool)
                                         then "a" else "not a")))

    /// Checks whether negation checking is sound and sufficiently complete.
    [<TestCaseSource("ObviousNegations")>]
    member x.``negates is sound and sufficiently complete`` a b =
        equivHolds (negates a b)
