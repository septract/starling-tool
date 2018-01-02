/// <summary>
///     Tests for <c>Starling.Core.Var</c>.
/// </summary>
module Starling.Tests.Core.Var

open NUnit.Framework

open Starling.Core.Expr
open Starling.Core.Var

/// <summary>
///     Tests for goal rewriting.
/// </summary>
module GoalRewriting =
    /// <summary>
    ///     NUnit tests for <c>Var</c>.
    /// </summary>
    type NUnit () =
        /// Test cases for testing goal rewriting.
        static member GoalConstants =
            [ TestCaseData( [ "foo"; "foo"; "foo"] )
                  .Returns( [ Goal (0I, "foo")
                              Goal (1I, "foo")
                              Goal (2I, "foo") ] )
              TestCaseData( ["foo"; "bar"; "baz"] )
                  .Returns( [ Goal (0I, "foo")
                              Goal (1I, "bar")
                              Goal (2I, "baz") ] ) ]

        /// Tests that the frame name generator works fine.
        [<TestCaseSource("GoalConstants")>]
        member x.``goal generation uses fresh variables properly`` xs =
            // TODO(CaptainHayashi): move this to AxiomTests.
            let fg = freshGen ()

            // The fun x boilerplate seems to be necessary.
            // Otherwise, mutations to fg apparently don't propagate!
            List.map (fun x -> goalVar fg x) xs
