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
    let check xs expectedExprList =
        match seqComposition xs with
        | BAnd ands ->
            Assert.AreEqual (Set.ofList expectedExprList, Set.ofList ands)
        | y -> Assert.Fail (sprintf "Expected %A but got %A" expectedExprList y)

    [<Test>]
    let ``Compose two basic assignments`` () =
        check
            <| [ bEq (sbAfter "foo") (sbBefore "bar")
                 bEq (sbAfter "baz") (sbBefore "foo") ]
            <| [ bEq (sbInter 0I "foo") (sbBefore "bar")
                 bEq (sbInter 0I "baz") (sbInter 0I "foo") ]

    [<Test>]
    let ``Compose two compositions`` () =
        check
            <| [ BAnd
                  [ bEq (sbInter 0I "foo") (sbBefore "bar")
                    bEq (sbAfter "baz") (sbInter 0I "foo") ]
                 BAnd
                  [ bEq (sbInter 0I "flop") (sbBefore "baz")
                    bEq (sbAfter "froz") (sbInter 0I "flop") ] ]
            <| [
                 bEq (sbInter 0I "foo") (sbBefore "bar")
                 bEq (sbInter 0I "baz") (sbInter 0I "foo")
                 bEq (sbInter 0I "flop") (sbInter 0I "baz")
                 bEq (sbInter 0I "froz") (sbInter 0I "flop")
               ]

    [<Test>]
    let ``Compose simple`` () =
        check
            <| [ bEq (sbAfter "t") (sbBefore "t")
                 bEq (sbAfter "g") (sbBefore "t") ]
            <| [ bEq (sbInter 0I "t") (sbBefore "t")
                 bEq (sbInter 0I "g") (sbInter 0I "t") ]

    [<Test>]
    let ``Compose multi`` () =
        check
            <| [ iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 1L)) ]
            <| [ iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (AInt 1L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (AInt 1L))
                 iEq (siInter 2I "t") (mkAdd2 (siInter 1I "t") (AInt 1L)) ]
    [<Test>]
    let ``Compose multi after`` () =
        check
            <| [ BAnd
                    [ (iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 1L)))
                      (iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 3L))) ]
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 1L)) ]
            <| [ iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (AInt 1L))
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t" )(AInt 3L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (AInt 1L)) ]

    [<Test>]
    let ``Compose multiCmd list`` () =
        check
            <| [ BAnd
                    [ (iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 1L)))
                      (iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 2L))) ]
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (AInt 3L))
                 iEq (siAfter "g") (siBefore "t") ]
            <| [ iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (AInt 1L))
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t" )(AInt 2L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t" )(AInt 3L))
                 iEq (siInter 0I "g") (siInter 1I "t") ]


module Frames =
    let check var expectedFramedExpr =
        Assert.AreEqual(expectedFramedExpr, frameVar Before var)

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
    let check command expectedValues =
        let actualValues =
            command
            |> semanticsOfCommand
                   (Starling.Lang.Modeller.coreSemantics)
                   (ticketLockModel.Globals)
                   (ticketLockModel.Locals)
            |> okOption
            |> Option.bind (function
                            | BAnd xs -> xs |> Set.ofList |> Some
                            | _ -> None)

        Assert.AreEqual(expectedValues, actualValues)

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
                iEq (siInter 0I "serving") (mkAdd2 (siBefore "serving") (AInt 1L))
            ])
