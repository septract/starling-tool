/// <summary>
///     Tests for <c>Starling.Core.Instantiate</c>.
/// </summary>
module Starling.Tests.Instantiate

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic
open Starling.Core.Instantiate

/// Tests for the func instantiation functions.
module Tests =
    /// Environment of test funcs.
    let TestFuncs =
        [ (dfunc "foo" [],
           iEq (AInt 5L : SVIntExpr) (AInt 6L))
          (dfunc "bar" [ Int "quux" ],
           iEq (siVar "quux") (AInt 6L))
          (dfunc "baz" [ Int "quux" ; Bool "flop" ],
           BAnd [sbVar "flop"; BGt (siVar "quux", siVar "quux")]) ]

    let testInstantiate =
        instantiate TestFuncs >> okOption
    let testInstantiateFail =
        instantiate TestFuncs >> failOption

    let none : Option<BoolExpr<Sym<MarkedVar>>> = None

    [<Test>]
    let ``Instantiate undefined func``() =
        Assert.That
            (testInstantiate (smexprfunc "nope" []),
             Is.EqualTo (Some none))
    [<Test>]
    let ``Instantiate func with no arguments``() =
        Assert.That
            (testInstantiate (smexprfunc "foo" []),
             Is.EqualTo
                (iEq (AInt 5L : SMIntExpr) (AInt 6L : SMIntExpr)
                 |> Some |> Some))
    [<Test>]
    let ``Instantiate func with one integer argument``() =
        Assert.That
            (testInstantiate (smexprfunc "bar" [ AInt 101L |> Expr.Int ]),
             Is.EqualTo
                (iEq (AInt 101L) (AInt 6L : SMIntExpr)
                 |> Some |> Some))
    [<Test>]
    let ``Instantiate func with two arguments of different types``() =
        Assert.That
            (testInstantiate
                (smexprfunc "baz"
                    [ siAfter "burble" |> Expr.Int
                      BTrue |> Expr.Bool ]),
             Is.EqualTo
                (BAnd [ BTrue; BGt (siAfter "burble", siAfter "burble") ]
                 |> Some |> Some))

    [<Test>]
    let ``Instantiate func with too many arguments``() =
        Assert.That
            (testInstantiateFail (smexprfunc "foo" [ AInt 101L |> Expr.Int ]),
             Is.EqualTo
                ([ CountMismatch(1, 0) ] |> Some))
    [<Test>]
    let ``Instantiate func with too few arguments``() =
        Assert.That
            (testInstantiateFail (smexprfunc "bar" []),
             Is.EqualTo
                ([ CountMismatch(0, 1) ] |> Some))
    [<Test>]
    let ``Instantiate func with two arguments of incorrect types``() =
        Assert.That
            (testInstantiateFail
                (smexprfunc "baz"
                    [ BTrue |> Expr.Bool
                      siAfter "burble" |> Expr.Int ]),
             Is.EqualTo
                ([ TypeMismatch (Int "quux", Bool ())
                   TypeMismatch (Bool "flop", Int ()) ] |> Some))
