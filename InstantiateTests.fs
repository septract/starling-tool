/// <summary>
///     Tests for <c>Starling.Core.Instantiate</c>.
/// </summary>
module Starling.Tests.Instantiate

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Utils.Testing
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic
open Starling.Core.Instantiate

/// Tests for the func instantiation functions.
module FuncInstantiate =
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
            (testInstantiate (smvfunc "nope" []),
             Is.EqualTo (Some none))
    [<Test>]
    let ``Instantiate func with no arguments``() =
        Assert.That
            (testInstantiate (smvfunc "foo" []),
             Is.EqualTo
                (iEq (AInt 5L : SMIntExpr) (AInt 6L : SMIntExpr)
                 |> Some |> Some))
    [<Test>]
    let ``Instantiate func with one integer argument``() =
        Assert.That
            (testInstantiate (smvfunc "bar" [ AInt 101L |> Expr.Int ]),
             Is.EqualTo
                (iEq (AInt 101L) (AInt 6L : SMIntExpr)
                 |> Some |> Some))
    [<Test>]
    let ``Instantiate func with two arguments of different types``() =
        Assert.That
            (testInstantiate
                (smvfunc "baz"
                    [ siAfter "burble" |> Expr.Int
                      BTrue |> Expr.Bool ]),
             Is.EqualTo
                (BAnd [ BTrue; BGt (siAfter "burble", siAfter "burble") ]
                 |> Some |> Some))

    [<Test>]
    let ``Instantiate func with too many arguments``() =
        Some
            [ BadFuncLookup
                (smvfunc "foo" [ AInt 101L |> Expr.Int ],
                 CountMismatch(1, 0)) ]
        ?=? testInstantiateFail (smvfunc "foo" [ AInt 101L |> Expr.Int ])
    let ``Instantiate func with too few arguments``() =
        Some
            [ BadFuncLookup
                (smvfunc "bar" [],
                 CountMismatch(0, 1)) ]
        ?=? testInstantiateFail (smvfunc "bar" [])
    [<Test>]
    let ``Instantiate func with two arguments of incorrect types``() =
        Some
            [ BadFuncLookup
                (smvfunc "baz"
                    [ BTrue |> Expr.Bool
                      siAfter "burble" |> Expr.Int ],
                 TypeMismatch (Int "quux", Bool ()))
              BadFuncLookup
                (smvfunc "baz"
                    [ BTrue |> Expr.Bool
                      siAfter "burble" |> Expr.Int ],
                 TypeMismatch (Bool "flop", Int ())) ]
        ?=?
            testInstantiateFail
                (smvfunc "baz"
                    [ BTrue |> Expr.Bool
                      siAfter "burble" |> Expr.Int ])
