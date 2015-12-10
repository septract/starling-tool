module Starling.Tests.Expander

open Fuchu
open Starling.Collections
open Starling.Expander
open Starling.Model
open Microsoft.Z3

let testResolvingCondViews ctx =
    testList "Test resolving CondViews to GuarViews" [
        testCase "Convert the empty CondView-list to the empty GuarView-list" <|
            fun _ -> Assert.Equal ("[| |] = <| |>",
                                   Multiset.empty (),
                                   resolveCondViews ctx (Multiset.empty ()))
        testCase "Convert a flat CondView-list to a GuarView-list with no guards" <|
            fun _ ->
                Assert.Equal
                    ("[| foo(bar), bar(baz) |] = <| ([], foo(bar)), ([], bar(baz)) |>",
                     Multiset.ofList
                         [ {GCond = ctx.MkTrue () ; GItem = {VName = "foo" ; VParams = [ctx.MkIntConst "bar" :> Expr] }}
                           {GCond = ctx.MkTrue () ; GItem = {VName = "bar" ; VParams = [ctx.MkIntConst "baz" :> Expr] }} ],
                     resolveCondViews
                         ctx
                         (Multiset.ofList
                              [CSetView {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }
                               CSetView {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] } ] ))
        testCase "Convert a singly-nested CondView-list to a GuarView-list with unit guards" <|
            fun _ ->
                Assert.Equal
                    ("[| if s then foo(bar) else bar(baz) |] = <| (s, foo(bar)) (not s, bar(baz)) |>",
                     Multiset.ofList
                         [ {GCond = ctx.MkBoolConst "s" ; GItem = {VName = "foo" ; VParams = [ctx.MkIntConst "bar" :> Expr] }}
                           {GCond = ctx.MkNot (ctx.MkBoolConst "s") ; GItem = {VName = "bar" ; VParams = [ctx.MkIntConst "baz" :> Expr] }} ],
                     resolveCondViews
                         ctx
                         (Multiset.ofList
                              [CITEView ((ctx.MkBoolConst "s"),
                                         Multiset.ofList
                                             [CSetView {VName = "foo" ; VParams = [ctx.MkIntConst "bar" :> Expr] } ],
                                         Multiset.ofList
                                             [CSetView {VName = "bar" ; VParams = [ctx.MkIntConst "baz" :> Expr] } ] ) ] ))
        testCase "Convert a complex-nested CondView-list to a GuarView-list with complex guards" <|
            fun _ ->
                Assert.Equal
                    ("[| if s then (if t then (foo(bar), bar(baz)) else fizz(buzz)), in(out) else ding(dong) |] = "
                     + "<| (s && t, foo(bar), bar(baz)) (s && not t, fizz(buzz)) (s, in(out)) (not s, ding(dong)) |>",
                     Multiset.ofList
                         [ {GCond = ctx.MkAnd [|ctx.MkBoolConst "s" ; ctx.MkBoolConst "t"|] ; GItem = {VName = "foo" ; VParams = [ctx.MkIntConst "bar" :> Expr] }}
                           {GCond = ctx.MkAnd [|ctx.MkBoolConst "s" ; ctx.MkBoolConst "t"|] ; GItem = {VName = "bar" ; VParams = [ctx.MkIntConst "baz" :> Expr] }}
                           {GCond = ctx.MkAnd [|ctx.MkBoolConst "s" ; ctx.MkNot (ctx.MkBoolConst "t")|] ; GItem = {VName = "fizz" ; VParams = [ctx.MkIntConst "buzz" :> Expr] }}
                           {GCond = ctx.MkBoolConst "s" ; GItem = {VName = "in" ; VParams = [ctx.MkIntConst "out" :> Expr] }}
                           {GCond = ctx.MkNot (ctx.MkBoolConst "s") ; GItem = {VName = "ding" ; VParams = [ctx.MkIntConst "dong" :> Expr] }} ],
                     resolveCondViews
                         ctx
                         (Multiset.ofList
                              [CITEView
                                   (ctx.MkBoolConst "s",
                                    Multiset.ofList
                                        [CITEView
                                             (ctx.MkBoolConst "t",
                                              Multiset.ofList
                                                  [CSetView {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }
                                                   CSetView {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] } ],
                                              Multiset.ofList
                                                  [CSetView {VName = "fizz" ; VParams = [ctx.MkIntConst "buzz"] } ] )
                                         CSetView {VName = "in" ; VParams = [ctx.MkIntConst "out"] } ],
                                    Multiset.ofList
                                        [CSetView {VName = "ding" ; VParams = [ctx.MkIntConst "dong"] } ] ) ] )) ]

[<Tests>]
let testExpander =
    let ctx = new Context ()

    let tl =
        testList "Test the expander"
                 [ testResolvingCondViews ctx ]

    ctx.Dispose ()

    tl

