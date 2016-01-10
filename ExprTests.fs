module Starling.Tests.Expr

open NUnit.Framework
open Starling.Expr

/// Tests for the expression types and functions.
type ExprTests() =
    /// Test cases for testing frame rewriting.
    static member FrameConstants =
        seq {
            yield (new TestCaseData(["foo"; "foo"; "foo"]))
                .Returns([Frame (0I, "foo")
                          Frame (1I, "foo")
                          Frame (2I, "foo")])
            yield (new TestCaseData(["foo"; "bar"; "baz"]))
                .Returns([Frame (0I, "foo")
                          Frame (1I, "bar")
                          Frame (2I, "baz")])
        }

    /// Tests that the frame name generator works fine.
    member x.``frame generation uses fresh variables properly`` xs =
        let fg = freshGen ()
        List.map (frame fg) xs

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
        arithMarkVars After (Set.ofList ["target1"; "target2"] |> inSet) expr
