module Starling.Tests.Core.Expr

open NUnit.Framework
open Starling.Core.Axiom
open Starling.Core.Expr
open Starling.Core.Sub


/// Tests for the expression types and functions.
type ExprTests() =
    /// Test cases for testing simple/compound arithmetic classification.
    static member ArithSimpleCompound =
        [ TestCaseData(AInt 1L)
            .Returns(false)
            .SetName("Classify '1' as simple")
          TestCaseData(AAdd [AInt 1L; AInt 2L])
            .Returns(true)
            .SetName("Classify '1+2' as compound")
          TestCaseData(ASub [AAdd [AInt 1L; AInt 2L]; AInt 3L])
            .Returns(true)
            .SetName("Classify '(1+2)-3' as compound")
          TestCaseData(aBefore "foo")
            .Returns(false)
            .SetName("Classify 'foo!before' as simple")
          TestCaseData(AMul [aBefore "foo"; aAfter "bar"])
            .Returns(true)
            .SetName("Classify 'foo!before * bar!after' as compound") ]

    /// Tests whether the simple/compound arithmetic patterns work correctly
    [<TestCaseSource("ArithSimpleCompound")>]
    member x.``SimpleArith and CompoundArith classify properly`` e =
        match e with
        | SimpleArith -> false
        | CompoundArith -> true

    /// Test cases for testing goal rewriting.
    static member GoalConstants =
        [ TestCaseData(["foo"; "foo"; "foo"])
                .Returns([Goal (0I, "foo")
                          Goal (1I, "foo")
                          Goal (2I, "foo")])
          TestCaseData(["foo"; "bar"; "baz"])
                .Returns([Goal (0I, "foo")
                          Goal (1I, "bar")
                          Goal (2I, "baz")])
        ]

    /// Tests that the frame name generator works fine.
    [<TestCaseSource("GoalConstants")>]
    member x.``goal generation uses fresh variables properly`` xs =
        // TODO(CaptainHayashi): move this to AxiomTests.
        let fg = freshGen ()

        // The fun x boilerplate seems to be necessary.
        // Otherwise, mutations to fg apparently don't propagate!
        List.map (fun x -> goalVar fg x) xs

    /// Test cases for testing constant post-state rewriting.
    static member ArithConstantPostStates =
        seq {
            yield (new TestCaseData(aUnmarked "target1"))
                .Returns(aAfter "target1")
                .SetName("Rewrite single target constant to post-state")
            yield (new TestCaseData(aUnmarked "notTarget"))
                .Returns(aUnmarked "notTarget")
                .SetName("Rewrite single non-target constant to post-state")
            yield (new TestCaseData(AAdd [AInt 4L; aUnmarked "target1"]))
                .Returns(AAdd [AInt 4L; aAfter "target1"])
                .SetName("Rewrite expression with one target constant to post-state")
            yield (new TestCaseData(ASub [aUnmarked "target1"; aUnmarked "target2"]))
                .Returns(ASub [aAfter "target1"; aAfter "target2"])
                .SetName("Rewrite expression with two target constants to post-state")
            yield (new TestCaseData(ADiv (AInt 6L, AInt 0L)))
                .Returns(ADiv (AInt 6L, AInt 0L))
                .SetName("Rewrite expression with no constants to post-state")
            yield (new TestCaseData(AMul [aUnmarked "foo"; aUnmarked "bar"]))
                .Returns(AMul [aUnmarked "foo"; aUnmarked "bar"])
                .SetName("Rewrite expression with two non-target constants to post-state")
        }

    [<TestCaseSource("ArithConstantPostStates")>]
    /// Tests whether rewriting constants in arithmetic expressions to post-state works.
    member x.``constants in arithmetic expressions can be rewritten to post-state`` expr =
        (liftMarker After (Set.ofList ["target1"; "target2"] |> inSet)).ASub expr
