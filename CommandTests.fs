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
        check [ Microcode.Assume (sbVar "x") ]

    [<Test>]
    let ``Reject baz <- Foo(bar) as a no-op``() =
        checkNot [ command "Foo" [ normalIntExpr (siVar "baz") ] [ normalIntExpr (siVar "bar") ] ]

    [<Test>]
    let ``Reject Assume (x!before); baz <- Foo(bar) as a no-op``() =
        checkNot
            [ Microcode.Assume (sbVar "x")
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
        check [ Microcode.Assume (sbVar "x") ]

    [<Test>]
    let ``Reject baz <- Foo(bar); Assume(x!before) as an Assume`` ()=
        checkNot [ command "Foo" [ normalIntExpr (siVar "baz") ] [ normalIntExpr (siVar "bar") ]
                   Microcode.Assume (sbVar "x") ]

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
            [ Microcode.Assume (sbVar "x") ]
            []

    [<Test>]
    let ``assumes are observable after a local stored command`` () =
        check true
            [ Microcode.Assume (sbVar "x") ]
            [ command "Foo" [ normalIntExpr (siVar "y") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``assumes are observable after a nonlocal stored command`` () =
        check true
            [ Microcode.Assume (sbVar "x") ]
            [ command "Foo" [ normalIntExpr (siVar "g") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``symbolics with are observable after the empty command`` () =
        check true
            [ Symbol [ SymString "foo" ] ]
            []

    [<Test>]
    let ``symbolics are observable after a local stored command`` () =
        check true
            [ Symbol [ SymString "foo" ] ]
            [ command "Foo" [ normalIntExpr (siVar "y") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``symbolics are observable after a nonlocal stored command`` () =
        check true
            [ Symbol [ SymString "foo" ] ]
            [ command "Foo" [ normalIntExpr (siVar "g") ] [ normalBoolExpr (sbVar "x") ] ]

    [<Test>]
    let ``local assignment is observable after a disjoint assignment`` () =
        check true
            [ normalIntExpr (siVar "y")
              *<- 
              normalIntExpr (mkInc (siVar "y")) ]
            [ normalIntExpr (siVar "g")
              *<-
              normalIntExpr (mkInc (siVar "y")) ]


    [<Test>]
    let ``local assignment is observable after a chained assignment`` () =
        check true
            [ normalIntExpr (siVar "y")
              *<-
              normalIntExpr (mkAdd2 (siVar "y") (IInt 1L)) ]
            [ normalIntExpr (siVar "g")
              *<-
              normalIntExpr (siVar "y") ]

    [<Test>]
    let ``local assignment is unobservable after an overwiting assignment`` () =
        check false
            [ normalIntExpr (siVar "y")
              *<-
              normalIntExpr (mkAdd2 (siVar "y") (IInt 1L)) ]
            [ normalIntExpr (siVar "y")
              *<-
              normalIntExpr (siVar "g") ]

