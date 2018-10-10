/// <summary>
///     Tests for <c>Starling.Core.Expr</c>.
/// </summary>
module Starling.Tests.Core.Expr

open NUnit.Framework

open Starling.Core.Expr

/// <summary>
///     Tests for expression classification.
/// </summary>
module Classifiers =
    /// <summary>
    ///     NUnit tests for <c>Expr</c>.
    /// </summary>
    type NUnit () =
        /// Test cases for testing simple/compound arithmetic classification.
        static member IntSimpleCompound =
            [ TestCaseData(IInt 1L)
                .Returns(false)
                .SetName("Classify '1' as simple")
              TestCaseData(IAdd [IInt 1L; IInt 2L])
                .Returns(true)
                .SetName("Classify '1+2' as compound")
              TestCaseData(ISub [IAdd [IInt 1L; IInt 2L]; IInt 3L])
                .Returns(true)
                .SetName("Classify '(1+2)-3' as compound")
              TestCaseData(IVar "foo")
                .Returns(false)
                .SetName("Classify 'foo' as simple")
              TestCaseData(IMul [IVar "foo"; IVar "bar"])
                .Returns(true)
                .SetName("Classify 'foo * bar' as compound") ]

        /// Tests whether the simple/compound arithmetic patterns work correctly
        [<TestCaseSource("IntSimpleCompound")>]
        member x.``SimpleInt and CompoundInt classify properly`` e =
            match e with
            | SimpleInt -> false
            | CompoundInt -> true

/// <summary>
///     Tests for expression simplification.
/// </sumary>
module ExprSimp =

  [<Test>]
  let ``Expression simplification on trivial conjunctions.`` () =
    Assert.AreEqual (
      (simp (BAnd [BTrue; BTrue])),
      BTrue
    )

  [<Test>]
  let ``Expression de-duplication, conjuction removal.`` () =
    Assert.AreEqual (
     simp (BAnd [ BEq
                   (normalIntExpr (IVar "foo"),
                    normalIntExpr (IVar "bar"));
                  BEq
                   (normalIntExpr (IVar "bar"),
                    normalIntExpr (IVar "foo"))
               ]),
     BEq (normalIntExpr (IVar "foo"),
          normalIntExpr (IVar "bar"))
   )

  [<Test>]
  let ``Expression de-duplication, disjunction removal.`` () =
    Assert.AreEqual (
     simp (BOr [ BEq
                   (normalIntExpr (IVar "foo"),
                    normalIntExpr (IVar "bar"));
                  BEq
                   (normalIntExpr (IVar "bar"),
                    normalIntExpr (IVar "foo"))
               ]),
     BEq (normalIntExpr (IVar "foo"),
          normalIntExpr (IVar "bar"))
   )
