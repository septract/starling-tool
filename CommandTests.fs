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
    let check n : unit =
        match n with
        | Queries.NopCmd _ -> ()
        | n ->
            Assert.Fail
                (Starling.Core.Pretty.printUnstyled
                    (Starling.Core.Pretty.headed
                        "Command is not a nop but should be one"
                        [ Pretty.printCommand n ] ))

    let checkNot n : unit =
        match n with
        | Queries.NopCmd _ ->
            Assert.Fail
                (Starling.Core.Pretty.printUnstyled
                    (Starling.Core.Pretty.headed
                        "Command is a nop but shouldn't be one"
                        [ Pretty.printCommand n ] ))
        | n -> ()

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

module Observable =
    open Starling.Core.Command.Queries
    open Starling.Core.Pretty

    let tvars =
        Map.ofList
            [ ("x", Bool (normalRec, ()))
              ("y", Int (normalRec, ())) ]

    let check v c d : unit =
        assertOkAndEqual
            v
            (isObservable tvars c d)
            (Starling.Core.Traversal.Pretty.printTraversalError (fun _ -> String "?")
             >> printUnstyled)

    [<Test>]
    let ``the empty command is unobservable after the empty command`` () =
        check false [] []

    [<Test>]
    let ``the empty command is unobservable after a local stored command`` () =
        check false
            []
            [ command "Foo" [ normalIntExpr (siVar "y") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``the empty command is unobservable after a nonlocal stored command`` () =
        check false
            []
            [ command "Foo" [ normalIntExpr (siVar "g") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``assumes are observable after the empty command`` () =
        check true
            [ command "Assume" [] [ normalBoolExpr (sbVar "x") ] ]
            []

    [<Test>]
    let ``assumes are observable after a local stored command`` () =
        check true
            [ command "Assume" [] [ normalBoolExpr (sbVar "x") ] ]
            [ command "Foo" [ normalIntExpr (siVar "y") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``assumes are observable after a nonlocal stored command`` () =
        check true
            [ command "Assume" [] [ normalBoolExpr (sbVar "x") ] ]
            [ command "Foo" [ normalIntExpr (siVar "g") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``symbolics with no havoc are observable after the empty command`` () =
        check true
            [ SymC { Symbol = { Sentence = [ SymString "foo" ]; Args = [] }
                     Working = Set.empty } ]
            []

    [<Test>]
    let ``symbolics with no havoc are observable after a local stored command`` () =
        check true
            [ SymC { Symbol = { Sentence = [ SymString "foo" ]; Args = [] }
                     Working = Set.empty } ]
            [ command "Foo" [ normalIntExpr (siVar "y") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``symbolics with no havoc are observable after a nonlocal stored command`` () =
        check true
            [ SymC { Symbol = { Sentence = [ SymString "foo" ]; Args = [] }
                     Working = Set.empty } ]
            [ command "Foo" [ normalIntExpr (siVar "g") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``local assignment is observable after a disjoint assignment`` () =
        check true
            [ Intrinsic
                (IAssign
                    { AssignType = Local
                      TypeRec = normalRec
                      LValue = siVar "y"
                      RValue = mkAdd2 (siVar "y") (IInt 1L) } ) ]
            [ Intrinsic
                (IAssign
                    { AssignType = Store
                      TypeRec = normalRec
                      LValue = siVar "g"
                      RValue = mkAdd2 (siVar "y") (IInt 1L) } ) ]


    [<Test>]
    let ``local assignment is observable after a chained assignment`` () =
        check true
            [ Intrinsic
                (IAssign
                    { AssignType = Local
                      TypeRec = normalRec
                      LValue = siVar "y"
                      RValue = mkAdd2 (siVar "y") (IInt 1L) } ) ]
            [ Intrinsic
                (IAssign
                    { AssignType = Store
                      TypeRec = normalRec
                      LValue = siVar "g"
                      RValue = siVar "y" } ) ]

    [<Test>]
    let ``local assignment is unobservable after an overwiting assignment`` () =
        check false
            [ Intrinsic
                (IAssign
                    { AssignType = Local
                      TypeRec = normalRec
                      LValue = siVar "y"
                      RValue = mkAdd2 (siVar "y") (IInt 1L) } ) ]
            [ Intrinsic
                (IAssign
                    { AssignType = Load
                      TypeRec = normalRec
                      LValue = siVar "y"
                      RValue = siVar "g" } ) ]

