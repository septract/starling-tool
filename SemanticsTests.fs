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
    let ``write map of x[3][i] <- 3; y[j] <- 4 is correct`` () =
        Map.ofList
            [ (Array (Array (Int (), Some 320, ()), Some 240, "x"),
               Indices <| Map.ofList
                [ (IInt 3L,
                    Indices <| Map.ofList
                        [ (IVar (Reg "i"), Entire (Int (IInt 3L))) ]) ] )
              (Array (Int (), Some 320, "y"),
               Indices <| Map.ofList
                [ (IVar (Reg "j"), Entire (Int (IInt 4L))) ] ) ]
        ?=?
        makeWriteMap
            [ (Int
                (IIdx
                    (Int (),
                     Some 320,
                     AIdx
                        (Array (Int (), Some 320, ()),
                         Some 240,
                         AVar (Reg "x"),
                         IInt 3L),
                     IVar (Reg "i"))),
               Int (IInt 3L))
              (Int
                (IIdx
                    (Int (),
                     Some 320,
                     AVar (Reg "y"),
                     (IVar (Reg "j")))),
               Int (IInt 4L)) ]

/// Shorthand for expressing an array update.
let aupd eltype length arr idx var =
    Array (eltype, length, AUpd (eltype, length, arr, idx, var))

module Normalisation =
    open Starling.Core.Pretty
    open Starling.Semantics.Pretty

    let checkAssigns expected actual : unit =
        assertOkAndEqual
            (Set.ofList expected)
            (lift Set.ofList (normaliseAssigns actual))
            (printSemanticsError >> printUnstyled)

    let checkMicrocode expected actual : unit =
        assertOkAndEqual
            (Set.ofList expected)
            (lift Set.ofList (normaliseMicrocode actual))
            (printSemanticsError >> printUnstyled)

    [<Test>]
    let ``assign normalisation of x[3][i] <- 3; y[j] <- 4 is correct`` () =
        checkAssigns
            [ (Array (Array (Int (), Some 320, ()), Some 240, "x"),
               aupd (Array (Int (), Some 320, ())) (Some 240) (AVar (Reg "x"))
                (IInt 3L)
                (aupd
                    (Int ())
                    (Some 320)
                    (AIdx
                        (Array (Int (), Some 320, ()),
                         Some 240,
                         AVar (Reg "x"),
                         IInt 3L))
                    (IVar (Reg "i"))
                    (Int (IInt 3L))))
              (Array (Int (), Some 320, "y"),
               aupd (Int()) (Some 320) (AVar (Reg "y"))
                    (IVar (Reg "j"))
                    (Int (IInt 4L))) ]
            [ (Int
                (IIdx
                    (Int (),
                     Some 320,
                     AIdx
                        (Array (Int (), Some 320, ()),
                         Some 240,
                         AVar (Reg "x"),
                         IInt 3L),
                     IVar (Reg "i"))),
               Int (IInt 3L))
              (Int
                (IIdx
                    (Int (),
                     Some 320,
                     AVar (Reg "y"),
                     (IVar (Reg "j")))),
               Int (IInt 4L)) ]

    [<Test>]
    let ``microcode normalisation of CAS(x[3], d[6], 2) is correct`` () =
        let xel = Int ()
        let xlen = Some 10
        let xname = "x"
        let xar = Array (xel, xlen, xname)
        let x3 = IIdx (xel, xlen, AVar (Reg xname), IInt 3L)
        let x3upd v = aupd xel xlen (AVar (Reg xname)) (IInt 3L) v

        let del = Int ()
        let dlen = Some 10
        let dname = "d"
        let dar = Array (del, dlen, dname)
        let d6 = IIdx (del, dlen, AVar (Reg dname), IInt 6L)
        let d6upd v = aupd del dlen (AVar (Reg dname)) (IInt 6L) v

        checkMicrocode
            // TODO(CaptainHayashi): order shouldn't matter in branches.
            [ Branch
                (iEq x3 d6,
                 [ Assign (dar, d6upd (Int d6))
                   Assign (xar, x3upd (Int (IInt 2L))) ],
                 [ Assign (dar, d6upd (Int x3))
                   Assign (xar, x3upd (Int x3)) ])
            ]
            [ Branch
                (iEq x3 d6,
                 [ Assign (Int x3, Int (IInt 2L))
                   Assign (Int d6, Int d6) ],
                 [ Assign (Int x3, Int x3)
                   Assign (Int d6, Int x3) ])
            ]

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
                             AVar (Reg "grid"),
                             (siVar "x")),
                         (siVar "y"))) ])
            (BEq
                (Array
                    (Array (Int (), Some 320, ()), Some 240,
                     AVar (Reg (After "grid"))),
                 aupd
                    (Array (Int (), Some 320, ()))
                    (Some 240)
                    (AVar (Reg (Before "grid")))
                    (siBefore "x")
                    (aupd
                        (Int ())
                        (Some 320)
                        (AIdx
                            (Array (Int (), Some 320, ()), Some 240,
                                AVar (Reg (Before "grid")),
                                siBefore "x"))
                        (siBefore "y")
                        (Int <| mkAdd2
                            (IIdx
                                (Int (),
                                 Some 320,
                                 AIdx
                                    (Array (Int (), Some 320, ()),
                                     Some 240,
                                     AVar (Reg (Before "grid")),
                                     (siBefore "x")),
                                 (siBefore "y")))
                            (IInt 1L)))))


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
              [ command "Assume" [] [ Expr.Bool <| iEq (siVar "s") (siVar "t") ]]
        <| Some (Set.ofList
                   [ iEq (siAfter "serving") (siBefore "serving")
                     iEq (siAfter "ticket") (siBefore "ticket")
                     iEq (siAfter "s") (siBefore "s")
                     iEq (siAfter "t") (siBefore "t")
                     iEq (siBefore "s") (siBefore "t") ])

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
                             AVar (Reg "grid"),
                             (siVar "x")),
                         (siVar "y"))) ]]
        <| Some (Set.ofList
            [ iEq (siAfter "x") (siBefore "x")
              iEq (siAfter "y") (siBefore "y")
              bEq (sbAfter "test") (sbBefore "test")
              (BEq
                (Array
                    (Array (Int (), Some 320, ()), Some 240,
                     AVar (Reg (After "grid"))),
                (Array
                    (Array (Int (), Some 320, ()), Some 240,
                     AVar (Reg (Intermediate (0I, "grid")))))))
              (BEq
                (Array
                    (Array (Int (), Some 320, ()), Some 240,
                     AVar (Reg (Intermediate (0I, "grid")))),
                 aupd
                    (Array (Int (), Some 320, ()))
                    (Some 240)
                    (AVar (Reg (Before "grid")))
                    (siBefore "x")
                    (aupd
                        (Int ())
                        (Some 320)
                        (AIdx
                            (Array (Int (), Some 320, ()), Some 240,
                                AVar (Reg (Before "grid")),
                                siBefore "x"))
                        (siBefore "y")
                        (Int <| mkAdd2
                            (IIdx
                                (Int (),
                                 Some 320,
                                 AIdx
                                    (Array (Int (), Some 320, ()),
                                     Some 240,
                                     AVar (Reg (Before "grid")),
                                     (siBefore "x")),
                                 (siBefore "y")))
                            (IInt 1L))))) ])

    [<Test>]
    let ``Semantically translate <serving++> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ command "!I++" [ Int (siVar "serving") ] [ Expr.Int <| siVar "serving" ] ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "serving") (siInter 0I "serving")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siInter 0I "serving") (mkAdd2 (siBefore "serving") (IInt 1L))
            ])
