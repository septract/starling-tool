module Starling.Tests.Expander

open Fuchu
open Starling.Expander
open Starling.Model
open Microsoft.Z3

let testResolvingCondViews ctx =
    testList "Test resolving CondViews to GuarViews" [
        testCase "Convert the empty CondView-list to the empty GuarView-list" <|
            fun _ -> Assert.Equal ("[| |] = <| |>",
                                   [],
                                   resolveCondViews ctx [])
        testCase "Convert a flat CondView-list to a GuarView-list with no guards" <|
            fun _ ->
                Assert.Equal
                    ("[| foo(bar), bar(baz) |] = <| ([], foo(bar)), ([], bar(baz)) |>",
                     [ {GCond = ctx.MkTrue () ; GView = {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }}
                       {GCond = ctx.MkTrue () ; GView = {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] }} ],
                     resolveCondViews
                         ctx
                         [CSetView {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }
                          CSetView {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] } ] )
        testCase "Convert a singly-nested CondView-list to a GuarView-list with unit guards" <|
            fun _ ->
                Assert.Equal
                    ("[| if s then foo(bar) else bar(baz) |] = <| (s, foo(bar)) (not s, bar(baz)) |>",
                     [ {GCond = ctx.MkBoolConst "s" ; GView = {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }}
                       {GCond = ctx.MkNot (ctx.MkBoolConst "s") ; GView = {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] }} ],
                     resolveCondViews
                         ctx
                         [CITEView ((ctx.MkBoolConst "s"),
                                    [CSetView {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] } ],
                                    [CSetView {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] } ] ) ] )
        testCase "Convert a complex-nested CondView-list to a GuarView-list with complex guards" <|
            fun _ ->
                Assert.Equal
                    ("[| if s then (if t then (foo(bar), bar(baz)) else fizz(buzz)), in(out) else ding(dong) |] = "
                     + "<| (s && t, foo(bar), bar(baz)) (s && not t, fizz(buzz)) (s, in(out)) (not s, ding(dong)) |>",
                     [ {GCond = ctx.MkAnd [|ctx.MkBoolConst "s" ; ctx.MkBoolConst "t"|] ; GView = {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }}
                       {GCond = ctx.MkAnd [|ctx.MkBoolConst "s" ; ctx.MkBoolConst "t"|] ; GView = {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] }}
                       {GCond = ctx.MkAnd [|ctx.MkBoolConst "s" ; ctx.MkNot (ctx.MkBoolConst "t")|] ; GView = {VName = "fizz" ; VParams = [ctx.MkIntConst "buzz"] }}
                       {GCond = ctx.MkBoolConst "s" ; GView = {VName = "in" ; VParams = [ctx.MkIntConst "out"] }}
                       {GCond = ctx.MkNot (ctx.MkBoolConst "s") ; GView = {VName = "ding" ; VParams = [ctx.MkIntConst "dong"] }} ],
                     resolveCondViews
                         ctx
                         [CITEView (ctx.MkBoolConst "s",
                                    [CITEView (ctx.MkBoolConst "t",
                                               [CSetView {VName = "foo" ; VParams = [ctx.MkIntConst "bar"] }
                                                CSetView {VName = "bar" ; VParams = [ctx.MkIntConst "baz"] } ],
                                               [CSetView {VName = "fizz" ; VParams = [ctx.MkIntConst "buzz"] } ] )
                                     CSetView {VName = "in" ; VParams = [ctx.MkIntConst "out"] } ],
                                    [CSetView {VName = "ding" ; VParams = [ctx.MkIntConst "dong"] } ] ) ] ) ]

[<Tests>]
let testExpander =
    let ctx = new Context ()

    let tl =
        testList "Test the expander"
                 [ testResolvingCondViews ctx ]

    ctx.Dispose ()

    tl

