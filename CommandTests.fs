/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Tests.Core.Command

open Starling.Core.TypeSystem
open NUnit.Framework

open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Command.Compose
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Expr

module Nops =
    let check a = Assert.IsTrue ( Queries.isNop [] )
    let checkNot a = Assert.IsTrue ( Queries.isNop [] )

    [<Test>]
    let ``Classify [] as a no-op``() =
        check []

    [<Test>]
    let ``Classify Assume(x!before) as a no-op``() =
        check [ command "Assume" [] [ SMExpr.Bool <| sbBefore "x" ] ]

    [<Test>]
    let ``Reject baz <- Foo(bar) as a no-op``() =
        checkNot [ command "Foo" [ Param.Int "baz" ] [ SMExpr.Int <| siBefore "bar" ] ]

    [<Test>]
    let ``Reject Assume (x!before); baz <- Foo(bar) as a no-op``() =
        checkNot
            [ command "Assume" [] [ SMExpr.Bool <| sbBefore "x" ] 
              command "Foo" [ Param.Int "baz" ] [ SMExpr.Int <| siBefore "bar" ] ]

module Assumes =
    let isAssume c =
        match c with
        | Queries.Assume _ -> true
        | _ -> false

    let check a    = Assert.IsTrue  ( isAssume a )
    let checkNot a = Assert.IsFalse ( isAssume a )

    [<Test>]
    let ``Reject [] as an assume``() =
        checkNot []

    [<Test>]
    let ``Classify Assume(x!before) as an assume``() =
        check [ command "Assume" [] [ SMExpr.Bool <| sbBefore "x" ] ]

    [<Test>]
    let ``Reject baz <- Foo(bar); Assume(x!before) as an Assume`` ()=
        checkNot [ command "Foo" [ Param.Int "baz" ] [ SMExpr.Int <| siBefore "bar" ]
                   command "Assume" [] [ SMExpr.Bool <| sbBefore "x" ] ]


    let checkIntermediate i e = Assert.AreEqual(i, nextIntermediate e)

    [<Test>]
    let ``nextIntermediate on Bool intermediate is one higher``() =
        checkIntermediate 6I <| SMExpr.Bool (sbInter 5I "foo")

    [<Test>]
    let ``nextIntermediate on 'not' passes through``() =
        checkIntermediate 11I <| SMExpr.Bool (BNot (sbInter 10I "bar"))

    [<Test>]
    let ``nextIntermediate on 'implies' is one higher than max``() =
        checkIntermediate 12I <| SMExpr.Bool (BImplies (sbInter 6I "a", sbInter 11I "b"))

    [<Test>]
    let ``nextIntermediate on 'add' is one higher than max``() =
        checkIntermediate 3I <| SMExpr.Int (AAdd [ siInter 1I "a";
                                                   siAfter "b";
                                                   siBefore "c";
                                                   siInter 2I "d"; ])
