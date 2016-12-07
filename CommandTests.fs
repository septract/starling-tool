/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Tests.Core.Command

open Starling.Core.TypeSystem
open NUnit.Framework
open Starling.Utils.Testing

open Starling.Core.Command
open Starling.Core.Command.Create
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
        check [ command "Assume" [] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``Reject baz <- Foo(bar) as a no-op``() =
        checkNot [ command "Foo" [ normalIntExpr (siVar "baz") ] [ normalIntExpr (siVar "bar") ] ]

    [<Test>]
    let ``Reject Assume (x!before); baz <- Foo(bar) as a no-op``() =
        checkNot
            [ command "Assume" [] [ normalBoolExpr (sbVar "x") ]
              command "Foo" [ normalIntExpr (siVar "baz") ] [ normalIntExpr (siVar "bar") ] ]

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
        check [ command "Assume" [] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``Reject baz <- Foo(bar); Assume(x!before) as an Assume`` ()=
        checkNot [ command "Foo" [ normalIntExpr (siVar "baz") ] [ normalIntExpr (siVar "bar") ]
                   command "Assume" [] [ normalBoolExpr (sbVar "x") ] ]
