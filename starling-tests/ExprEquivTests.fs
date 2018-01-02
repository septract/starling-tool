/// <summary>
///     Tests for <c>Starling.Core.ExprEquiv</c>.
/// </summary>
module Starling.Tests.ExprEquiv

open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.Core.Expr
open Starling.Core.ExprEquiv
open Starling.Core.Pretty
open Starling.Core.Var
open Starling.Core.Var.Pretty

/// <summary>
///     NUnit tests for <c>ExprEquiv</c>.
/// </summary>
type NUnit () =
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
                  (iEq (IInt 5L) (IInt 6L) : VBoolExpr) |])
            .Returns(true)
          (tcd [| (iEq (IVar "x") (IInt 2L))
                  (BNot (iEq (IVar "x") (IInt 2L))) |])
            .Returns(true)
          (tcd [| (iEq (IVar "x") (IInt 2L))
                  (BNot (iEq (IVar "y") (IInt 2L))) |])
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
                                         |> printVBoolExpr |> printUnstyled)
                                        (((d.OriginalArguments.[0])
                                          :?> VBoolExpr)
                                         |> printVBoolExpr |> printUnstyled)
                                        (if (d.ExpectedResult :?> bool)
                                         then "a" else "not a")))

    /// Checks whether negation checking is sound and sufficiently complete.
    [<TestCaseSource("ObviousNegations")>]
    member x.``negates is sound and sufficiently complete`` a b =
        negates id a b