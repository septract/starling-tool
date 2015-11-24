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
                     [ {GCond = Set.empty ; GView = {VName = "foo" ; VParams = ["bar"] }}
                       {GCond = Set.empty ; GView = {VName = "bar" ; VParams = ["baz"] }} ],
                     resolveCondViews
                         ctx
                         [CSetView {VName = "foo" ; VParams = ["bar"] }
                          CSetView {VName = "bar" ; VParams = ["baz"] } ] )
        testCase "Convert a singly-nested CondView-list to a GuarView-list with unit guards" <|
            fun _ ->
                Assert.Equal
                    ("[| if s then foo(bar) else bar(baz) |] = <| (s, foo(bar)) (not s, bar(baz)) |>",
                     [ {GCond = new Set<BoolExpr> ( [ctx.MkBoolConst "s"] ) ; GView = {VName = "foo" ; VParams = ["bar"] }}
                       {GCond = new Set<BoolExpr> ( [ctx.MkNot (ctx.MkBoolConst "s") ] ) ; GView = {VName = "bar" ; VParams = ["baz"] }} ],
                     resolveCondViews
                         ctx
                         [CITEView ((ctx.MkBoolConst "s"),
                                    [CSetView {VName = "foo" ; VParams = ["bar"] } ],
                                    [CSetView {VName = "bar" ; VParams = ["baz"] } ] ) ] )
        testCase "Convert a complex-nested CondView-list to a GuarView-list with complex guards" <|
            fun _ ->
                Assert.Equal
                    ("[| if s then (if t then (foo(bar), bar(baz)) else fizz(buzz)), in(out) else ding(dong) |] = "
                     + "<| (s && t, foo(bar), bar(baz)) (s && not t, fizz(buzz)) (s, in(out)) (not s, ding(dong)) |>",
                     [ {GCond = new Set<BoolExpr> ( [ctx.MkBoolConst "t" ; ctx.MkBoolConst "s"] ) ; GView = {VName = "foo" ; VParams = ["bar"] }}
                       {GCond = new Set<BoolExpr> ( [ctx.MkBoolConst "t" ; ctx.MkBoolConst "s"] ) ; GView = {VName = "bar" ; VParams = ["baz"] }}
                       {GCond = new Set<BoolExpr> ( [ctx.MkNot (ctx.MkBoolConst "t") ; ctx.MkBoolConst "s"] ) ; GView = {VName = "fizz" ; VParams = ["buzz"] }}
                       {GCond = new Set<BoolExpr> ( [ctx.MkBoolConst "s"] ) ; GView = {VName = "in" ; VParams = ["out"] }}
                       {GCond = new Set<BoolExpr> ( [ctx.MkNot (ctx.MkBoolConst "s") ] ) ; GView = {VName = "ding" ; VParams = ["dong"] }} ],
                     resolveCondViews
                         ctx
                         [CITEView (ctx.MkBoolConst "s",
                                    [CITEView (ctx.MkBoolConst "t",
                                               [CSetView {VName = "foo" ; VParams = ["bar"] }
                                                CSetView {VName = "bar" ; VParams = ["baz"] } ],
                                               [CSetView {VName = "fizz" ; VParams = ["buzz"] } ] )
                                     CSetView {VName = "in" ; VParams = ["out"] } ],
                                    [CSetView {VName = "ding" ; VParams = ["dong"] } ] ) ] ) ]

[<Tests>]
let testExpander =
    let ctx = new Context ()

    let tl =
        testList "Test the expander"
                 [ testResolvingCondViews ctx ]

    ctx.Dispose ()

    tl

