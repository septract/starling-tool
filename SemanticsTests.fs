/// <summary>
///    Tests for <c>Starling.Core.Semantics</c>.
/// </summary>
module Starling.Tests.Semantics

open Chessie.ErrorHandling
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
        | Ok (BAnd ands, _) ->
            assertEqual (Set.ofList expectedExprList) (Set.ofList ands)
        | Bad x ->
            Assert.Fail (sprintf "sequential composition failed: %A" x)
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
            <| [ iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 1L)) ]
            <| [ iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L))
                 iEq (siInter 2I "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ]
    [<Test>]
    let ``Compose multi after`` () =
        check
            <| [ BAnd
                    [ (iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 1L)))
                      (iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 3L))) ]
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 1L)) ]
            <| [ iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t" )(IInt 3L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L)) ]

    [<Test>]
    let ``Compose multiCmd list`` () =
        check
            <| [ BAnd
                    [ (iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 1L)))
                      (iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 2L))) ]
                 iEq (siAfter "t") (mkAdd2 (siBefore "t") (IInt 3L))
                 iEq (siAfter "g") (siBefore "t") ]
            <| [ iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t" )(IInt 2L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t" )(IInt 3L))
                 iEq (siInter 0I "g") (siInter 1I "t") ]


module WriteMaps =
    [<Test>]
    let ``write map of x[3][i] = y[j]++ is correct`` () =
        Map.ofList
            [ (Reg "x",
                Indices <| Map.ofList
                    [ (IVar (Reg "i"),
                        Indices <| Map.ofList
                            [ (IInt 3L, Entire) ]) ] )
              (Reg "y",
                Indices <| Map.ofList
                    [ (IVar (Reg "j"), Entire ) ] ) ]
        ?=?
        makeWriteMap
            (command "!ILoad++"
                [ Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg "x"),
                             IInt 3L),
                         IVar (Reg "i")))
                  Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AVar (Reg "y"),
                         (IVar (Reg "j")))) ]
                [ Expr.Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AVar (Reg (Before "y")),
                         (siBefore "j"))) ])

module Frames =
    let check var expectedFramedExpr =
        expectedFramedExpr ?=? (frameVar Before var)

    let checkExpr expr framedExpr =
        assertOkAndEqual
            framedExpr
            (frame
                (ticketLockModel.SharedVars)
                (ticketLockModel.ThreadVars)
                expr)
            (Starling.Core.Traversal.Pretty.printTraversalError
                Starling.Semantics.Pretty.printSemanticsError
             >> Starling.Core.Pretty.printUnstyled)

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


let testShared =
    Map.ofList
        [ ("grid",
            Type.Array
                (Type.Array (Type.Int (), Some 320, ()),
                    Some 240,
                    ()))
          ("test", Type.Bool ()) ]

let testThread =
    Map.ofList
        [ ("x", Type.Int ())
          ("y", Type.Int ()) ]


module PrimInstantiateTests =
    let check svars tvars prim expectedValues =
        let actualValues =
            instantiateSemanticsOfPrim (Starling.Lang.Modeller.coreSemantics)
                prim
        let pError =
            Starling.Semantics.Pretty.printSemanticsError
            >> Starling.Core.Pretty.printUnstyled

        assertOkAndEqual expectedValues actualValues pError

    [<Test>]
    let ``Instantiate <grid[x][y]++>``() =
        check testShared testThread
            (command "!I++"
                [ Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg "grid"),
                             IVar (Reg "x")),
                         IVar (Reg "y"))) ]
                [ Expr.Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg (Before "grid")),
                             (siBefore "x")),
                         (siBefore "y"))) ])
                (iEq
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg (After "grid")),
                             (siBefore "x")),
                         (siBefore "y")))
                    (mkAdd2
                        (IIdx
                            (Int (),
                             Some 320,
                             AIdx
                                (Array (Int (), Some 320, ()),
                                 Some 240,
                                 AVar (Reg (Before "grid")),
                                 (siBefore "x")),
                             (siBefore "y")))
                        (IInt 1L)))


module CommandTests =
    let check svars tvars command expectedValues =
        let actualValues =
            command
            |> semanticsOfCommand
                   (Starling.Lang.Modeller.coreSemantics)
                   svars
                   tvars
            |> lift (function
                     | { Semantics = BAnd xs } -> xs |> Set.ofList |> Some
                     | _ -> None)

        let pError =
            Starling.Semantics.Pretty.printSemanticsError
            >> Starling.Core.Pretty.printUnstyled

        assertOkAndEqual expectedValues actualValues pError

    [<Test>]
    let ``Semantically translate <assume(s == t)> using the ticket lock model`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ command "Assume" [] [ Expr.Bool <| iEq (siBefore "s") (siBefore "t") ]]
        <| Some (Set.ofList
                   [ iEq (siAfter "serving") (siBefore "serving")
                     iEq (siAfter "ticket") (siBefore "ticket")
                     iEq (siAfter "s") (siBefore "s")
                     iEq (siAfter "t") (siBefore "t")
                     iEq (siBefore "s") (siBefore "t") ])

(*
    [<Test>]
    let ``Semantically translate <grid[x][y]++> using the test environments``() =
        check testShared testThread
            [ command "!I++"
                [ Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg "grid"),
                             IVar (Reg "x")),
                         IVar (Reg "y"))) ]
                [ Expr.Int
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg (Before "grid")),
                             (siBefore "x")),
                         (siBefore "y"))) ]]
        <| Some (Set.ofList
            [
                // TODO: frame for grid
                iEq (siAfter "x") (siBefore "x")
                iEq (siAfter "y") (siBefore "y")
                bEq (sbAfter "test") (sbBefore "test")
                iEq
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg (After "grid")),
                             (siBefore "x")),
                         (siBefore "y")))
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg (Intermediate (0I, "grid"))),
                             (siBefore "x")),
                         (siBefore "after")))
                iEq
                    (IIdx
                        (Int (),
                         Some 320,
                         AIdx
                            (Array (Int (), Some 320, ()),
                             Some 240,
                             AVar (Reg (Intermediate (0I, "grid"))),
                             (siBefore "x")),
                         (siBefore "after")))
                    (mkAdd2
                        (IIdx
                            (Int (),
                             Some 320,
                             AIdx
                                (Array (Int (), Some 320, ()),
                                 Some 240,
                                 AVar (Reg (Before "grid")),
                                 (siBefore "x")),
                             (siBefore "after")))
                        (IInt 1L))
            ])
*)

    [<Test>]
    let ``Semantically translate <serving++> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ command "!I++" [ Int (siVar "serving") ] [ Expr.Int <| siBefore "serving" ] ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "serving") (siInter 0I "serving")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siInter 0I "serving") (mkAdd2 (siBefore "serving") (IInt 1L))
            ])
