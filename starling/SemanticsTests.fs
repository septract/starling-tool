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


/// <summary>
///     Tests for instruction capping.
/// </summary>
module Cap =
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty
    open Starling.Semantics.Pretty

    /// <summary>
    ///     Checks the capped instruction generated from an assign map against
    ///     a given instruction.
    /// </summary>
    /// <param name="expectedMap">The expected capped instruction.</param>
    /// <param name="expectedInstr">The expected capped instructions.</param>
    /// <param name="map">The assign map to use.</param>
    /// <param name="instr">The instructions to cap.</param>
    let check
      (expectedMap : Map<TypedVar, MarkedVar>)
      (expectedInstrs : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>, unit> list)
      (map : Map<TypedVar, MarkedVar>)
      (instrs : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>, unit> list)
      : unit =
        assertOkAndEqual
            (expectedMap, expectedInstrs)
            (capInstructions map instrs)
            (printTraversalError printSemanticsError >> printUnstyled)

    [<Test>]
    let ``capping rewrites lvalues in assignments`` () =
        check
            (Map.ofList
                [ (Int (normalRec, "foo"), After "foo")
                  (Int (normalRec, "bar"), Before "bar") ])
            [ Assign
                (Int (normalRec, After "foo"),
                 Some (Expr.Int (normalRec, IVar (Reg (Intermediate (4I, "foo")))))) ]
            (Map.ofList
                [ (Int (normalRec, "foo"), Intermediate (5I, "foo"))
                  (Int (normalRec, "bar"), Before "bar") ])
            [ Assign
                (Int (normalRec, Intermediate (5I, "foo")),
                 Some (Expr.Int (normalRec, IVar (Reg (Intermediate (4I, "foo")))))) ]

    [<Test>]
    let ``capping rewrites rvalues in assignments`` () =
        check
            (Map.ofList
                [ (Int (normalRec, "foo"), After "foo")
                  (Int (normalRec, "bar"), After "bar") ])
            [ Assign
                (Int (normalRec, After "foo"),
                 Some (Expr.Int (normalRec, IVar (Reg (After "bar"))))) ]
            (Map.ofList
                [ (Int (normalRec, "foo"), After ("foo"))
                  (Int (normalRec, "bar"), Intermediate (2I, "bar")) ])
            [ Assign
                (Int (normalRec, After "foo"),
                 Some (Expr.Int (normalRec, IVar (Reg (Intermediate (2I, "bar")))))) ]

    [<Test>]
    let ``capping rewrites lvalues and rvalues in assignments`` () =
        check
            (Map.ofList
                [ (Int (normalRec, "foo"), After "foo")
                  (Int (normalRec, "bar"), After "bar") ])
            [ Assign
                (Int (normalRec, After "foo"),
                 Some (Expr.Int (normalRec, IVar (Reg (After "bar"))))) ]
            (Map.ofList
                [ (Int (normalRec, "foo"), Intermediate (5I, "foo"))
                  (Int (normalRec, "bar"), Intermediate (2I, "bar")) ])
            [ Assign
                (Int (normalRec, Intermediate (5I, "foo")),
                 Some (Expr.Int (normalRec, IVar (Reg (Intermediate (2I, "bar")))))) ]

    [<Test>]
    let ``ticket lock example is capped properly`` () =
        check 
            (Map.ofList
                [ (Int (normalRec, "t"), After "t")
                  (Int (normalRec, "s"), After "s")
                  (Int (normalRec, "serving"), Before "serving")
                  (Int (normalRec, "ticket"), Before "ticket") ] )
            [ Int (normalRec, After "t") *<- normalIntExpr (siBefore "serving")
              Int (normalRec, After "s") *<- normalIntExpr (siAfter "t") ]
            (Map.ofList
                [ (Int (normalRec, "t"), Intermediate (0I, "t"))
                  (Int (normalRec, "s"), Intermediate (0I, "s"))
                  (Int (normalRec, "serving"), Before "serving")
                  (Int (normalRec, "ticket"), Before "ticket") ] )
            [ Int (normalRec, Intermediate (0I, "t")) *<- normalIntExpr (siBefore "serving")
              Int (normalRec, Intermediate (0I, "s")) *<- normalIntExpr (IVar (Reg (Intermediate (0I, "t")))) ]


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

    let checkMicrocode expected actual : unit =
        assertOkAndEqual
            (Set.ofList expected)
            (lift Set.ofList (normaliseMicrocode actual))
            (printSemanticsError >> printUnstyled)

    [<Test>]
    let ``microcode normalisation of x[3][i] <- 3; y[j] <- 4 is correct`` () =
        checkMicrocode
            [ Assign
                (TypedVar.Array
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
              Assign
                (TypedVar.Array
                    (mkArrayTypeRec (Int (normalRec, ())) (Some 320), "y"),
                Some <| aupd
                    (mkTypedArrayExpr
                            (Int (normalRec, ()))
                            (Some 320)
                            (AVar (Reg "y")))
                    (IVar (Reg "j"))
                    (normalIntExpr (IInt 4L))) ]
            [ Assign
                (normalIntExpr
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
              Assign
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
            [ Branch
                (iEq x3 d6,
                 [ xar *<- x3upd (normalIntExpr (IInt 2L))
                   dar *<- d6upd (normalIntExpr d6) ],
                 [ xar *<- x3upd (normalIntExpr x3)
                   dar *<- d6upd (normalIntExpr x3) ])
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
///     Tests for microcode processing.
/// </summary>
module ProcessMicrocode =
    /// <summary>
    ///     Checks a microcode instruction set against an expected
    ///     processed instruction set and assignment map.
    /// </summary>
    /// <param name="cap">Whether to cap final intermediates.</param>
    /// <param name="svars">The context shared variables.</param>
    /// <param name="tvars">The context thread variables.</param>
    /// <param name="expectedMap">The expected assignment map.</param>
    /// <param name="expectedInstrs">The expected final instructions.</param>
    /// <param name="instrs">The instructions to convert.</param>
    let check (cap : bool) (svars : VarMap) (tvars : VarMap)
      (expectedMap : Map<TypedVar, MarkedVar>)
      (expectedInstrs : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>, unit> list)
      (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>, unit> list)
      : unit =
        let svars = VarMap.toTypedVarSeq svars
        let tvars = VarMap.toTypedVarSeq tvars
        let vars = List.ofSeq (Seq.append svars tvars)

        let proc =
            if cap
            then processMicrocodeRoutine
            else processMicrocodeRoutineUncapped

        let processedR = proc vars instrs

        assertOkAndEqual
            (expectedInstrs, expectedMap)
            processedR
            (Pretty.printSemanticsError >> Core.Pretty.printUnstyled)
     
    [<Test>]
    let ``chained assigns are processed properly`` () =
        check false ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (Map.ofList
                [ (Int (normalRec, "t"), Intermediate (0I, "t"))
                  (Int (normalRec, "s"), Intermediate (0I, "s"))
                  (Int (normalRec, "serving"), Before "serving")
                  (Int (normalRec, "ticket"), Before "ticket") ] )
            [ Int (normalRec, Intermediate (0I, "t")) *<- normalIntExpr (siBefore "serving")
              Int (normalRec, Intermediate (0I, "s")) *<- normalIntExpr (IVar (Reg (Intermediate (0I, "t")))) ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving")
              normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ]
   
    [<Test>]
    let ``chained assigns are processed and capped properly`` () =
        check true ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (Map.ofList
                [ (Int (normalRec, "t"), After "t")
                  (Int (normalRec, "s"), After "s")
                  (Int (normalRec, "serving"), Before "serving")
                  (Int (normalRec, "ticket"), Before "ticket") ] )
            [ Int (normalRec, After "t") *<- normalIntExpr (siBefore "serving")
              Int (normalRec, After "s") *<- normalIntExpr (siAfter "t") ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving")
              normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ]

    [<Test>]
    let ``unequal branches are processed and capped properly`` () =
        check true ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (Map.ofList
                [ (Int (normalRec, "t"), After "t")
                  (Int (normalRec, "s"), After "s")
                  (Int (normalRec, "serving"), Before "serving")
                  (Int (normalRec, "ticket"), Before "ticket") ] )
            [ Branch
                (BEq (normalIntExpr (siBefore "t"), normalIntExpr (siBefore "ticket")),
                 [ Int (normalRec, After "t") *<- normalIntExpr (siBefore "serving")
                   Int (normalRec, After "s") *<- normalIntExpr (siBefore "s") ],
                 [ Int (normalRec, After "s") *<- normalIntExpr (siBefore "serving")
                   Int (normalRec, After "t") *<- normalIntExpr (siBefore "t") ]) ]
            [ Branch
                (BEq (normalIntExpr (siVar "t"), normalIntExpr (siVar "ticket")),
                 [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving") ],
                 [ normalIntExpr (siVar "s") *<- normalIntExpr (siVar "serving") ]) ]


/// <summary>
///     Tests for microcode compilation to Boolean expressions.
/// </summary>
module MicrocodeToBool =
    /// <summary>
    ///     Checks a microcode instruction set against an expected
    ///     Boolean expression.
    /// </summary>
    /// <param name="svars">The context shared variables.</param>
    /// <param name="tvars">The context thread variables.</param>
    /// <param name="expected">The expected expression.</param>
    /// <param name="instrs">The instructions to convert.</param>
    let check
      (svars : VarMap)
      (tvars : VarMap)
      (expected : BoolExpr<Sym<MarkedVar>> list)
      (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>, unit> list)
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
            (BAnd (List.sort (List.map trySort expected)))
            (lift trySort microcodeR)
            (Pretty.printSemanticsError >> Core.Pretty.printUnstyled)

    [<Test>]
    let ``the empty command is translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siAfter "t") (siBefore "t") ]
            []

    [<Test>]
    let ``lone assumes are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siAfter "t") (siBefore "t")
              iEq (siBefore "s") (siBefore "t") ]
            [ Assume (iEq (siVar "s") (siVar "t")) ]

    [<Test>]
    let ``lone havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "t") (siBefore "t") ]
            [ havoc (normalIntExpr (siVar "s")) ]

    [<Test>]
    let ``lone assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "t")
              iEq (siAfter "t") (siBefore "t") ]
            [ normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ]

    [<Test>]
    let ``chained assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siAfter "t")
              iEq (siAfter "t") (siBefore "serving") ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving")
              normalIntExpr (siVar "s") *<- normalIntExpr (siVar "t") ]

    [<Test>]
    let ``chained assigns and assumptions are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siBefore "s") (siAfter "t")
              iEq (siAfter "t") (siBefore "serving") ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving")
              Assume (iEq (siVar "s") (siVar "t")) ]

    [<Test>]
    let ``well-formed branches are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              (mkImplies
                (iEq (siBefore "s") (siBefore "t"))
                (iEq (siAfter "t") (siBefore "serving")))
              (mkImplies
                (mkNot (iEq (siBefore "s") (siBefore "t")))
                (iEq (siAfter "t") (siBefore "ticket"))) ]
            [ Branch
                  (iEq (siVar "s") (siVar "t"),
                     [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "serving") ],
                     [ normalIntExpr (siVar "t") *<- normalIntExpr (siVar "ticket") ]) ]

    [<Test>]
    let ``long compositions are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
              iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L))
              iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
              normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
              normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]

    [<Test>]
    let ``pre-state havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L))
              iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ]
            [ havoc (normalIntExpr (siVar "t"))
              normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
              normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]

    [<Test>]
    let ``intermediate havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
              iEq (siAfter "t") (mkAdd2 (siInter 1I "t") (IInt 1L)) ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
              havoc (normalIntExpr (siVar "t"))
              normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L)) ]

    [<Test>]
    let ``post-state havocs are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            [ iEq (siAfter "serving") (siBefore "serving")
              iEq (siAfter "ticket") (siBefore "ticket")
              iEq (siAfter "s") (siBefore "s")
              iEq (siInter 0I "t") (mkAdd2 (siBefore "t") (IInt 1L))
              iEq (siInter 1I "t") (mkAdd2 (siInter 0I "t") (IInt 1L)) ]
            [ normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
              normalIntExpr (siVar "t") *<- normalIntExpr (mkAdd2 (siVar "t") (IInt 1L))
              havoc (normalIntExpr (siVar "t")) ]

    [<Test>]
    let ``single-dimensional arrays are normalised and translated properly`` () =
        check testShared2 testThread
             [ iEq (siAfter "x") (siBefore "x")
               iEq (siAfter "y") (siBefore "y")
               BEq
                 (typedArrayToExpr
                     (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg (Intermediate (0I, "foo"))))),
                  aupd
                     (mkTypedArrayExpr
                         (Bool (normalRec, ()))
                         (Some 10)
                         (AVar (Reg (Before "foo"))))
                     (siBefore "x")
                     (normalBoolExpr BTrue))
               BEq
                 (typedArrayToExpr
                     (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg (After "foo")))),
                  aupd
                     (mkTypedArrayExpr
                         (Bool (normalRec, ()))
                         (Some 10)
                         (AVar (Reg (Intermediate (0I, "foo")))))
                     (siBefore "y")
                     (normalBoolExpr BFalse)) ]
            [ normalBoolExpr
                  (BIdx
                      (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg "foo")),
                       IVar (Reg "x")))
              *<- normalBoolExpr BTrue
              normalBoolExpr
                  (BIdx
                      (mkTypedArrayExpr (Bool (normalRec, ())) (Some 10) (AVar (Reg "foo")),
                       IVar (Reg "y")))
              *<- normalBoolExpr BFalse ]

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
            [ iEq (siAfter "x") (siBefore "x")
              iEq (siAfter "y") (siBefore "y")
              bEq (sbAfter "test") (sbBefore "test")
              BEq
                (typedArrayToExpr (grid After),
                 aupd (grid Before) (siBefore "x")
                    (aupd (gridx Before) (siBefore "y")
                        (normalIntExpr <| mkAdd2
                            (IIdx ((gridx Before), siBefore "y"))
                            (IInt 1L)))) ]
            [ normalIntExpr
                 (IIdx (gridxv, IVar (Reg "y")))
              *<-
              normalIntExpr
                  (mkAdd2
                      (IIdx (gridxv, siVar "y"))
                      (IInt 1L)) ]


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
              [ Assume (iEq (siVar "s") (siVar "t")) ]
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
            [ normalIntExpr (IIdx (gridxv, siVar "y"))
              *<- normalIntExpr (mkInc (IIdx (gridxv, siVar "y"))) ]
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
    let ``Semantically translate <%{foo([|serving|]}> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ Symbol
                    [ SymString "foo("
                      SymArg (normalIntExpr (siVar "serving") )
                      SymString ")" ] ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "serving") (siBefore "serving")
                BVar (
                    Sym
                        [ SymString "foo("
                          SymArg (normalIntExpr (siBefore "serving") )
                          SymString ")" ]
                )
            ])

    [<Test>]
    let ``Semantically translate <serving++> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ normalIntExpr (siVar "serving") *<- normalIntExpr (mkInc (siVar "serving")) ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "serving") (mkAdd2 (siBefore "serving") (IInt 1L))
            ])
