/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Tests.Core.Command

open Starling.Core.TypeSystem
open NUnit.Framework
open Starling.Utils.Testing

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


    let checkIntermediate v i e = assertEqual i (getIntermediate v e)

    [<Test>]
    let ``getIntermediate on given Bool intermediate returns its intermediate``() =
        checkIntermediate "foo" (Some 5I) (normalBoolExpr (sbInter 5I "foo"))

    [<Test>]
    let ``getIntermediate on given Bool before returns nothing``() =
        checkIntermediate "foo" None (normalBoolExpr (sbBefore "foo"))

    [<Test>]
    let ``getIntermediate on given Bool after returns nothing``() =
        checkIntermediate "foo" None (normalBoolExpr (sbAfter "foo"))

    [<Test>]
    let ``getIntermediate on other Bool intermediate returns nothing``() =
        checkIntermediate "bar" None (normalBoolExpr (sbInter 5I "foo"))

    [<Test>]
    let ``getIntermediate on other Bool before returns nothing``() =
        checkIntermediate "bar" None (normalBoolExpr (sbBefore "foo"))

    [<Test>]
    let ``getIntermediate on other Bool after returns nothing``() =
        checkIntermediate "bar" None (normalBoolExpr (sbAfter "foo"))

    [<Test>]
    let ``getIntermediate on given Int intermediate returns its intermediate``() =
        checkIntermediate "foo" (Some 10I) (normalIntExpr (siInter 10I "foo"))

    [<Test>]
    let ``getIntermediate on given Int before returns nothing``() =
        checkIntermediate "foo" None (normalIntExpr (siBefore "foo"))

    [<Test>]
    let ``getIntermediate on given Int after returns nothing``() =
        checkIntermediate "foo" None (normalIntExpr (siAfter "foo"))

    [<Test>]
    let ``getIntermediate on other Int intermediate returns nothing``() =
        checkIntermediate "bar" None (normalIntExpr (siInter 5I "foo"))

    [<Test>]
    let ``getIntermediate on other Int before returns nothing``() =
        checkIntermediate "bar" None (normalIntExpr (siBefore "foo"))

    [<Test>]
    let ``getIntermediate on other Int after returns nothing``() =
        checkIntermediate "bar" None (normalIntExpr (siAfter "foo"))

    [<Test>]
    let ``getIntermediate on 'not' passes through``() =
        checkIntermediate "bar" (Some 10I) (normalBoolExpr (BNot (sbInter 10I "bar")))

    [<Test>]
    let ``getIntermediate on 'implies' is max of its arguments matching the name``() =
        checkIntermediate "a" (Some 6I)
            (normalBoolExpr (BImplies (sbInter 6I "a", sbInter 11I "b")))

    [<Test>]
    let ``getIntermediate on 'add' is max of the addends matching the name``() =
        checkIntermediate "a" (Some 2I)
            (normalIntExpr
                (IAdd
                    [ siInter 1I "a"
                      siAfter "b"
                      siInter 3I "b"
                      siBefore "c"
                      siInter 2I "a" ]))

    [<Test>]
    let ``getIntermediate on 'modulo' is max of its arguments matching the name`` () =
        checkIntermediate "a" (Some 11I)
            (normalIntExpr (IMod (siInter 6I "a", siInter 11I "a")))
