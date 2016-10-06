/// <summary>
///     Tests for the guarder.
/// </summary>
module Starling.Tests.Guarder

open NUnit.Framework
open Starling.Utils.Testing
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Core.View
open Starling.Lang.Modeller
open Starling.Lang.Guarder


/// Tests for the view guarder.
module Tests =
    let oneGFunc (cnd : BoolExpr<Sym<Var>>) (name : string)
      (ps : Expr<Sym<Var>> list)
      : IteratedGFunc<Sym<Var>> =
        iteratedGFunc cnd name ps (AInt 1L)

    [<Test>]
    let ``Convert the empty CView to the empty GView`` () =
        assertEqual
            (Multiset.empty : IteratedGView<Sym<Var>>)
            (guardCView (Multiset.empty : CView))

    [<Test>]
    let ``Convert a flat CondView-list to a GuarView-list with no guard`` () =
        assertEqual
            (Multiset.ofFlatList
                [ oneGFunc BTrue "foo" [ Expr.Int (siVar "bar") ]
                  oneGFunc BTrue "bar" [ Expr.Int (siVar "baz") ]] )
            (guardCView
                (Multiset.ofFlatList
                    [ iterated
                        (Func <| svfunc "foo" [ Expr.Int (siVar "bar") ])
                        None
                      iterated
                        (Func <| svfunc "bar" [ Expr.Int (siVar "baz") ] )
                        None ] ))

    [<Test>]
    let ``Convert a singly-nested CondView-list to a GuarView-list with unit guard`` () =
        assertEqual
            (Multiset.ofFlatList
                [ oneGFunc (sbVar "s") "foo" [ Expr.Int (siVar "bar") ]
                  oneGFunc (BNot (sbVar "s")) "bar" [ Expr.Int (siVar "baz") ]] )
            (guardCView <| Multiset.ofFlatList
                [ iterated
                    (CFunc.ITE
                        (sbVar "s",
                         Multiset.ofFlatList
                            [ iterated
                                (Func <| svfunc "foo" [ Expr.Int (siVar "bar") ] )
                                None ],
                         Multiset.ofFlatList
                            [ iterated
                                (Func <| svfunc "bar" [ Expr.Int (siVar "baz") ] )
                                None ] ))
                    None ] )

    [<Test>]
    let ``Convert a complex-nested CondView-list to a GuarView-list with complex guards`` () =
        assertEqual
            (Multiset.ofFlatList
                [ oneGFunc (BAnd [ sbVar "s"; sbVar "t" ] )
                    "foo"
                    [ Expr.Int (siVar "bar") ]
                  oneGFunc (BAnd [ sbVar "s"; sbVar "t" ] )
                    "bar"
                    [ Expr.Int (siVar "baz") ]
                  oneGFunc (BAnd [ sbVar "s"; BNot (sbVar "t") ] )
                    "fizz"
                    [ Expr.Int (siVar "buzz") ]
                  oneGFunc (sbVar "s")
                    "in"
                    [ Expr.Int (siVar "out") ]
                  oneGFunc (BNot (sbVar "s"))
                    "ding"
                    [ Expr.Int (siVar "dong") ]] )
            (guardCView <| Multiset.ofFlatList
                [ iterated
                    (CFunc.ITE
                        (sbVar "s",
                         Multiset.ofFlatList
                            [ iterated
                                (CFunc.ITE
                                    (sbVar "t",
                                        Multiset.ofFlatList
                                            [ iterated
                                                (Func <| svfunc
                                                    "foo"
                                                    [ Expr.Int (siVar "bar") ] )
                                                None
                                              iterated
                                                (Func <| svfunc
                                                    "bar"
                                                    [ Expr.Int (siVar "baz") ] )
                                                None],
                                        Multiset.ofFlatList
                                            [ iterated
                                                (Func <| svfunc
                                                    "fizz"
                                                    [ Expr.Int (siVar "buzz") ] )
                                                None]))
                                None
                              iterated
                                (Func <| svfunc
                                    "in"
                                    [ Expr.Int (siVar "out") ])
                                None],
                         Multiset.ofFlatList
                            [ iterated
                                (Func <| svfunc
                                    "ding"
                                    [ Expr.Int (siVar "dong") ])
                                None] ))
                    None ] )
