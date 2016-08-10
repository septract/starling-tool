/// <summary>
///    Tests for <c>Starling.Core.Semantics</c>.
/// </summary>
module Starling.Tests.Semantics

open NUnit.Framework
open Starling
open Starling.Collections
open Starling.Utils
open Starling.Utils.Testing
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.Var
open Starling.Core.Model
open Starling.Semantics
open Starling.Tests.Studies

/// Tests for the semantic transformer.
module Compositions =
    let check x y expr =
        Assert.AreEqual(composeBools x y, expr)

    [<Test>]
    let ``Compose two basic assignments`` () =
        check
            <| bEq (sbAfter "foo") (sbBefore "bar")
            <| bEq (sbAfter "baz") (sbBefore "foo")
            <| BAnd [ bEq (sbInter 0I "foo") (sbBefore "bar")
                      bEq (sbAfter "baz") (sbInter 0I "foo") ]

    [<Test>]
    let ``Compose two compositions`` () =
        check
            <| BAnd
                  [ bEq (sbInter 0I "foo") (sbBefore "bar")
                    bEq (sbAfter "baz") (sbInter 0I "foo") ]
            <| BAnd
                  [ bEq (sbInter 0I "flop") (sbBefore "baz")
                    bEq (sbAfter "froz") (sbInter 0I "flop") ]
            <| BAnd
                   [ bEq (sbInter 1I "baz") (sbInter 0I "foo")
                     bEq (sbInter 0I "foo") (sbBefore "bar")
                     bEq (sbAfter "froz") (sbInter 2I "flop")
                     bEq (sbInter 2I "flop") (sbInter 1I "baz") ]

module Frames =
    let check var framedExpr =
        Assert.AreEqual(frameVar Before var, framedExpr)

    let checkExpr expr framedExpr =
        let actualExpr =
            frame
                (ticketLockModel.Globals)
                (ticketLockModel.Locals)
                expr

        Assert.AreEqual(actualExpr, framedExpr)

    [<Test>]
    let ``Frame an integer variable`` () =
        check (Int "foo") (iEq (siAfter "foo") (siBefore "foo"))

    [<Test>]
    let ``Frame a boolean variable`` () =
        check (Bool "bar") (bEq (sbAfter "bar") (sbBefore "bar"))

    // Test cases for the expression framer.
    [<Test>]
    let ``Frame id using the ticket lock model`` () =
        checkExpr BTrue 
              <| [ iEq (siAfter "serving") (siBefore "serving")
                   iEq (siAfter "ticket") (siBefore "ticket")
                   iEq (siAfter "s") (siBefore "s")
                   iEq (siAfter "t") (siBefore "t") ]

    [<Test>]
    let ``Frame a simple command expression using the ticket lock model`` () =
          checkExpr
            <| BAnd
                   [ BGt(siAfter "ticket", siBefore "ticket")
                     BLe(siAfter "serving", siBefore "serving")
                     iEq (siBefore "s") (siBefore "t") ]

            <| [ iEq (siAfter "s") (siBefore "s")
                 iEq (siAfter "t") (siBefore "t") ]

module CommandTests =
    let check command values =
        let vals =
            command
            |> semanticsOfCommand
                   (Starling.Lang.Modeller.coreSemantics)
                   (ticketLockModel.Globals)
                   (ticketLockModel.Locals)
            |> okOption
            |> Option.bind (function
                            | BAnd xs -> xs |> Set.ofList |> Some
                            | _ -> None)

        Assert.AreEqual(values, vals, message=sprintf "Expected: ``%A``, but got: ``%A``" vals values)

    [<Test>]
    let ``Semantically translate <assume(s == t)> using the ticket lock model`` () =
        check [ command "Assume" [] [ Expr.Bool <| iEq (siBefore "s") (siBefore "t") ]]
        <| Some (Set.ofList
                   [ iEq (siAfter "serving") (siBefore "serving")
                     iEq (siAfter "ticket") (siBefore "ticket")
                     iEq (siAfter "s") (siBefore "s")
                     iEq (siAfter "t") (siBefore "t")
                     iEq (siBefore "s") (siBefore "t") ])

    [<Test>]
    let ``Semantically translate <serving++> using the ticket lock model``() =
        check [ command "!I++" [ Int "serving" ] [ Expr.Int <| siBefore "serving" ] ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "serving") (siInter 0I "serving")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siInter 0I "serving") (iAdd (siBefore "serving") (AInt 1L))
            ])
