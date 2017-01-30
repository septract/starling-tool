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


module WriteMaps =
    [<Test>]
    let ``variable and index path of x[3][i] <- 3 is correct`` () =
        Some
            (TypedVar.Array
                (mkArrayTypeRec
                    (mkArrayType
                        (Int (normalRec, ()))
                        (Some 320))
                    (Some 240),
                 "x"),
             [ IInt 3L; IVar (Reg "i") ])
        ?=? varAndIdxPath
                (normalIntExpr
                    (IIdx
                        (mkTypedSub
                             (mkArrayTypeRec (Int (normalRec, ())) (Some 320))
                             (AIdx
                                 (mkTypedSub
                                    (mkArrayTypeRec
                                        (mkArrayType (Int (normalRec, ())) (Some 320))
                                        (Some 240))
                                    (AVar (Reg "x")),
                                  IInt 3L)),
                         IVar (Reg "i"))))

    [<Test>]
    let ``write map of x[3][i] <- 3; y[j] <- 4 is correct`` () =
        Map.ofList
            [ (Array
                (mkArrayTypeRec
                    (mkArrayType (Int (normalRec, ())) (Some 320))
                    (Some 240),
                    "x"),
               Indices <| Map.ofList
                [ (IInt 3L,
                    Indices <| Map.ofList
                        [ (IVar (Reg "i"), Entire (Some (normalIntExpr (IInt 3L)))) ]) ] )
              (Array
                (mkArrayTypeRec (Int (normalRec, ())) (Some 320), "y"),
               Indices <| Map.ofList
                [ (IVar (Reg "j"), Entire (Some (normalIntExpr (IInt 4L)))) ] ) ]
        ?=?
        makeWriteMap
            [ (normalIntExpr
                (IIdx
                    (mkTypedSub
                         (mkArrayTypeRec (Int (normalRec, ())) (Some 320))
                         (AIdx
                             (mkTypedSub
                                (mkArrayTypeRec
                                    (mkArrayType (Int (normalRec, ())) (Some 320))
                                    (Some 240))
                                (AVar (Reg "x")),
                              IInt 3L)),
                     IVar (Reg "i"))),
               Some (Int (normalRec, IInt 3L)))
              (normalIntExpr
                (IIdx
                    (mkTypedSub
                        (mkArrayTypeRec (Int (normalRec, ())) (Some 320))
                        (AVar (Reg "y")),
                     (IVar (Reg "j")))),
               Some (Int (normalRec, IInt 4L))) ]

/// Shorthand for expressing an array update.
let aupd' arr idx var : ArrayExpr<'Var> =
    AUpd (stripTypeRec arr, idx, var)
let aupd arr idx var =
    typedArrayToExpr (mkTypedSub arr.SRec (aupd' arr idx var))


/// <summary>
///     Tests for frame generation.
/// </summary>
module MakeFrame =
    /// <summary>
    ///     Checks the frame generated from an assign map against a given
    ///     Boolean expression.
    /// </summary>
    /// <param name="expected">The expected list of frame expressions.</param>
    /// <param name="toFrame">The assign map to convert to a frame.</param>
    let check
      (expected : BoolExpr<Sym<MarkedVar>> list)
      (toFrame : Map<TypedVar, MarkedVar>)
      : unit =
        List.sort expected ?=? List.sort (makeFrame toFrame) 

    [<Test>]
    let ``the empty assign list generates the empty frame`` () =
        check [] Map.empty

    [<Test>]
    let ``only non-after variables are framed`` () =
        check
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "t") (siInter 0I "t") ]
            (Map.ofList
                [ (Int (normalRec, "serving"), Before "serving")
                  (Int (normalRec, "ticket"), Before "ticket")
                  (Int (normalRec, "t"), Intermediate (0I, "t"))
                  (Int (normalRec, "s"), After "s") ] )


/// <summary>
///     Tests for microcode normalisation.
/// </summary>
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
            [ (TypedVar.Array
                   (mkArrayTypeRec
                        (mkArrayType
                            (Int (normalRec, ()))
                            (Some 320))
                        (Some 240),
                        "x"),
               Some <| aupd
                   (mkTypedArrayExpr
                        (mkArrayType (Int (normalRec, ())) (Some 320))
                        (Some 240)
                        (AVar (Reg "x")))
                   (IInt 3L)
                   (aupd
                        (mkTypedArrayExpr
                            (Int (normalRec, ()))
                            (Some 320)
                            (AIdx
                                (mkTypedArrayExpr
                                    (mkArrayType (Int (normalRec, ())) (Some 320))
                                    (Some 240)
                                    (AVar (Reg "x")),
                                 IInt 3L)))
                        (IVar (Reg "i"))
                        (normalIntExpr (IInt 3L))))
              (TypedVar.Array
                   (mkArrayTypeRec (Int (normalRec, ())) (Some 320), "y"),
               Some <| aupd
                   (mkTypedArrayExpr
                        (Int (normalRec, ()))
                        (Some 320)
                        (AVar (Reg "y")))
                   (IVar (Reg "j"))
                   (normalIntExpr (IInt 4L))) ]
            [ (normalIntExpr
                (IIdx
                    (mkTypedArrayExpr
                         (Int (normalRec, ()))
                         (Some 320)
                         (AIdx
                             (mkTypedArrayExpr
                                 (mkArrayType (Int (normalRec, ())) (Some 320))
                                 (Some 240)
                                 (AVar (Reg "x")),
                              IInt 3L)),
                     IVar (Reg "i"))),
               Some (normalIntExpr (IInt 3L)))
              (normalIntExpr
                (IIdx
                    (mkTypedArrayExpr
                        (Int (normalRec, ()))
                        (Some 320)
                        (AVar (Reg "y")),
                     (IVar (Reg "j")))),
               Some (normalIntExpr (IInt 4L))) ]

    [<Test>]
    let ``microcode normalisation of CAS(x[3], d[6], 2) is correct`` () =
        let xel = Int (normalRec, ())
        let xlen = Some 10
        let xname = "x"
        let xtr = mkArrayTypeRec xel xlen
        let xar = Array (xtr, xname)
        let xav = mkTypedSub xtr (AVar (Reg xname))
        let x3 = IIdx (xav, IInt 3L)
        let x3upd v = aupd xav (IInt 3L) v

        let del = Int (normalRec, ())
        let dlen = Some 10
        let dname = "d"
        let dtr = mkArrayTypeRec del dlen
        let dar = Array (dtr, dname)
        let dav = mkTypedSub dtr (AVar (Reg dname))
        let d6 = IIdx (dav, IInt 6L)
        let d6upd v = aupd dav (IInt 6L) v

        checkMicrocode
            // TODO(CaptainHayashi): order shouldn't matter in branches.
            [ Branch
                (iEq x3 d6,
                 [ dar *<- d6upd (normalIntExpr d6)
                   xar *<- x3upd (normalIntExpr (IInt 2L)) ],
                 [ dar *<- d6upd (normalIntExpr x3)
                   xar *<- x3upd (normalIntExpr x3) ])
            ]
            [ Branch
                (iEq x3 d6,
                 [ normalIntExpr x3 *<- normalIntExpr (IInt 2L)
                   normalIntExpr d6 *<- normalIntExpr d6 ],
                 [ normalIntExpr x3 *<- normalIntExpr x3
                   normalIntExpr d6 *<- normalIntExpr x3 ])
            ]


let testShared =
    Map.ofList
        [ ("grid",
            mkArrayType
                (mkArrayType (Type.Int (normalRec, ())) (Some 320))
                (Some 240))
          ("test", Type.Bool (normalRec, ())) ]

let testShared2 =
    Map.ofList
        [ ("foo", mkArrayType (Type.Bool (normalRec, ())) (Some 10)) ]

let testThread =
    Map.ofList
        [ ("x", Type.Int (normalRec, ()))
          ("y", Type.Int (normalRec, ())) ]


/// <summary>
///     Tests for microcode compilation to Boolean expressions.
/// </summary>
module MicrocodeToBool =
    /// <summary>
    ///     Checks a microcode instruction set against an expected
    ///     Boolean expression.
    /// </summary>
    /// <param name="expected">The expected expression.</param>
    /// <param name="instrs">The instructions to convert.</param>
    let check
      (svars : VarMap)
      (tvars : VarMap)
      (expected : BoolExpr<Sym<MarkedVar>>)
      (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>> list list)
      : unit =
        // Try to make the check order-independent.
        let rec trySort bool =
            match bool with
            | BAnd xs -> BAnd (List.sort (List.map trySort xs))
            | BOr xs -> BOr (List.sort (List.map trySort xs))
            | x -> x

        let svars = VarMap.toTypedVarSeq svars
        let tvars = VarMap.toTypedVarSeq tvars
        let vars = List.ofSeq (Seq.append svars tvars)

        let processedR = processMicrocodeRoutine vars instrs
        let microcodeR = lift (uncurry microcodeRoutineToBool) processedR

        assertOkAndEqual
            (trySort expected)
            (lift trySort microcodeR)
            (Pretty.printSemanticsError >> Core.Pretty.printUnstyled)

    [<Test>]
    let ``the empty command is translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "s")
                  iEq (siAfter "t") (siBefore "t") ] )
            []

    [<Test>]
    let ``the singleton empty command is translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "s")
                  iEq (siAfter "t") (siBefore "t") ] )
            [ [] ]

    [<Test>]
    let ``a composition of empty commands is translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "s")
                  iEq (siAfter "t") (siBefore "t") ] )
            [ []; []; []; ]

    [<Test>]
    let ``lone assumes are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "s")
                  iEq (siAfter "t") (siBefore "t")
                  iEq (siBefore "s") (siBefore "t") ])
            [ [ Assume (iEq (siVar "s") (siVar "t")) ] ]

    [<Test>]
    let ``lone havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "t") (siBefore "t") ])
            [ [ havoc (normalIntExpr (siVar "s")) ] ]

    [<Test>]
    let ``lone assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "t")
                  iEq (siAfter "t") (siBefore "t") ])
            [ [ normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ] ]

    [<Test>]
    let ``unchained assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "t")
                  iEq (siAfter "t") (siBefore "t")
                  iEq (siInter 0I "s") (siBefore "serving") ])
            [ [ normalIntExpr (siVar "s") *<- normalIntExpr (siVar "serving") ]
              [ normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ]  ]

    [<Test>]
    let ``chained assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siInter 0I "t")
                  iEq (siAfter "t") (siInter 0I "t")
                  iEq (siInter 0I "t") (siBefore "serving") ])
            [ [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving") ]
              [ normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ] ]

    [<Test>]
    let ``chained assigns and assumptions are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "s")
                  iEq (siBefore "s") (siInter 0I "t")
                  iEq (siAfter "t") (siInter 0I "t")
                  iEq (siInter 0I "t") (siBefore "serving") ])
            [ [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving") ]
              [ Assume (iEq (siVar "s") (siVar "t")) ] ]

    [<Test>]
    let ``well-formed branches are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "s")
                  (mkImplies
                    (iEq (siBefore "s") (siBefore "t"))
                    (iEq (siAfter "t") (siBefore "serving")))
                  (mkImplies
                    (mkNot (iEq (siBefore "s") (siBefore "t")))
                    (iEq (siAfter "t") (siBefore "ticket"))) ])
            [ [ Branch
                    (iEq (siVar "s") (siVar "t"),
                     [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving") ],
                     [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "ticket") ]) ] ]

    [<Test>]
    let ``long compositions are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
               [ iEq (siAfter "serving") (siBefore "serving")
                 iEq (siAfter "ticket") (siBefore "ticket")
                 iEq (siAfter "s") (siBefore "s")
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ] )
            [ [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ] ]

    [<Test>]
    let ``parallel compositions are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
               [ iEq (siAfter "serving") (siBefore "serving")
                 iEq (siAfter "ticket") (siBefore "ticket")
                 iEq (siInter 0I "s") (mkSub2 (siBefore "s") (IInt 1L))
                 iEq (siInter 1I "s") (mkSub2 (siInter 0I "s") (IInt 1L))
                 iEq (siAfter "s") (mkSub2 (siInter 1I "s") (IInt 1L))
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ] )
            [ [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
                normalIntExpr (siVar "s") *<- normalIntExpr (mkSub2 (siVar "s") (IInt 1L)) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
                normalIntExpr (siVar "s") *<- normalIntExpr (mkSub2 (siVar "s") (IInt 1L)) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
                normalIntExpr (siVar "s") *<- normalIntExpr (mkSub2 (siVar "s") (IInt 1L)) ] ]

    [<Test>]
    let ``pre-state havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
               [ iEq (siAfter "serving") (siBefore "serving")
                 iEq (siAfter "ticket") (siBefore "ticket")
                 iEq (siAfter "s") (siBefore "s")
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ] )
            [ [ havoc (normalIntExpr (siVar "t")) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ] ]

    [<Test>]
    let ``intermediate havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
               [ iEq (siAfter "serving") (siBefore "serving")
                 iEq (siAfter "ticket") (siBefore "ticket")
                 iEq (siAfter "s") (siBefore "s")
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ] )
            [ [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ havoc (normalIntExpr (siVar "t")) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ] ]

    [<Test>]
    let ``post-state havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
               [ iEq (siAfter "serving") (siBefore "serving")
                 iEq (siAfter "ticket") (siBefore "ticket")
                 iEq (siAfter "s") (siBefore "s")
                 iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
                 iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L)) ] )
            [ [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ havoc (normalIntExpr (siVar "t")) ] ]

    [<Test>]
    let ``single-dimensional arrays are normalised and translated properly`` () =
        check testShared2 testThread
            (BAnd
                [ iEq (siAfter "x") (siBefore "x")
                  iEq (siAfter "y") (siBefore "y")
                  BEq
                    (typedArrayToExpr
                        (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg (After "foo")))),
                     aupd
                        (mkTypedArrayExpr
                            (Bool (normalRec, ()))
                            (Some 10)
                            (aupd'
                                (mkTypedArrayExpr
                                    (Bool (normalRec, ()))
                                    (Some 10)
                                    (AVar (Reg (Before "foo"))))
                                (siBefore "x")
                                (normalBoolExpr BTrue)))
                        (siBefore "y")
                        (normalBoolExpr  BFalse)) ])
            [ [ normalBoolExpr
                    (BIdx
                        (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg "foo")),
                         IVar (Reg "x")))
                *<- normalBoolExpr BTrue
                normalBoolExpr
                    (BIdx
                        (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg "foo")),
                         IVar (Reg "y")))
                *<- normalBoolExpr BFalse ] ]

    [<Test>]
    let ``multi-dimensional arrays are normalised and translated properly`` () =
        let grid marker = 
            (mkTypedArrayExpr
                (mkArrayType (Int (normalRec, ())) (Some 320))
                (Some 240)
                (AVar (Reg (marker "grid"))))
        let gridx marker =
            (mkTypedArrayExpr
                (Int (normalRec, ()))
                (Some 320)
                (AIdx (grid marker, IVar (Reg (marker "x")))))

        let gridv = 
            (mkTypedArrayExpr
                (mkArrayType (Int (normalRec, ())) (Some 320))
                (Some 240)
                (AVar (Reg "grid")))
        let gridxv =
            (mkTypedArrayExpr
                (Int (normalRec, ()))
                (Some 320)
                (AIdx (gridv, siVar "x")))

        check testShared testThread
            (BAnd
                [ iEq (siAfter "x") (siBefore "x")
                  iEq (siAfter "y") (siBefore "y")
                  bEq (sbAfter "test") (sbBefore "test")
                  BEq
                    (typedArrayToExpr (grid After),
                     aupd (grid Before) (siBefore "x")
                        (aupd (gridx Before) (siBefore "y")
                            (normalIntExpr <| mkAdd2
                                (IIdx ((gridx Before), siBefore "y"))
                                (IInt 1L)))) ] )
            [ [ normalIntExpr
                   (IIdx (gridxv, IVar (Reg "y")))
                *<-
                normalIntExpr
                    (mkAdd2
                        (IIdx (gridxv, siVar "y"))
                        (IInt 1L)) ] ]


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
              [ command "Assume" [] [ normalBoolExpr <| iEq (siVar "s") (siVar "t") ]]
        <| Some (Set.ofList
                   [ iEq (siAfter "serving") (siBefore "serving")
                     iEq (siAfter "ticket") (siBefore "ticket")
                     iEq (siAfter "s") (siBefore "s")
                     iEq (siAfter "t") (siBefore "t")
                     iEq (siBefore "s") (siBefore "t") ])

    [<Test>]
    let ``Semantically translate <grid[x][y]++> using the test environments``() =
        let grid marker = 
            (mkTypedArrayExpr
                (mkArrayType (Int (normalRec, ())) (Some 320))
                (Some 240)
                (AVar (Reg (marker "grid"))))
        let gridx marker =
            (mkTypedArrayExpr
                (Int (normalRec, ()))
                (Some 320)
                (AIdx (grid marker, IVar (Reg (marker "x")))))

        let gridv = 
            (mkTypedArrayExpr
                (mkArrayType (Int (normalRec, ())) (Some 320))
                (Some 240)
                (AVar (Reg "grid")))
        let gridxv =
            (mkTypedArrayExpr
                (Int (normalRec, ()))
                (Some 320)
                (AIdx (gridv, siVar "x")))

        check testShared testThread
            [ command "!I++"
                [ normalIntExpr (IIdx (gridxv, siVar "y")) ]
            [ normalIntExpr (IIdx (gridxv, siVar "y")) ] ]
        <| Some (Set.ofList
            [ iEq (siAfter "x") (siBefore "x")
              iEq (siAfter "y") (siBefore "y")
              bEq (sbAfter "test") (sbBefore "test")
              BEq
                (typedArrayToExpr (grid After),
                 aupd (grid Before) (siBefore "x")
                    (aupd (gridx Before) (siBefore "y")
                        (normalIntExpr <| mkAdd2
                            (IIdx (gridx Before, siBefore "y"))
                            (IInt 1L)))) ] )

    [<Test>]
    let ``Semantically translate <%{foo(#1)}(serving)> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ SymC
                    { Sentence = [ SymString "foo("; SymParamRef 1; SymString ")" ]
                      Args = [ normalIntExpr (siVar "serving") ] } ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "serving") (siBefore "serving")
                BVar (
                    sym [ SymString "foo("; SymParamRef 1; SymString ")" ]
                        [ normalIntExpr (siBefore "serving") ]
                )
            ])

    [<Test>]
    let ``Semantically translate <serving++> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ command "!I++" [ normalIntExpr (siVar "serving") ] [ normalIntExpr <| siVar "serving" ] ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "serving") (mkAdd2 (siBefore "serving") (IInt 1L))
            ])
