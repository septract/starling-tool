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
    let ``write map of x[3][i] <- 3; y[j] <- 4 is correct`` () =
        Map.ofList
            [ (Array (Array (Int (), Some 320, ()), Some 240, "x"),
               Indices <| Map.ofList
                [ (IInt 3L,
                    Indices <| Map.ofList
                        [ (IVar (Reg "i"), Entire (Some (Int (IInt 3L)))) ]) ] )
              (Array (Int (), Some 320, "y"),
               Indices <| Map.ofList
                [ (IVar (Reg "j"), Entire (Some (Int (IInt 4L)))) ] ) ]
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
               Some (Int (IInt 3L)))
              (Int
                (IIdx
                    (Int (),
                     Some 320,
                     AVar (Reg "y"),
                     (IVar (Reg "j")))),
               Some (Int (IInt 4L))) ]

/// Shorthand for expressing an array update.
let aupd' eltype length arr idx var =
    AUpd (eltype, length, arr, idx, var)
let aupd eltype length arr idx var =
    Array (eltype, length, aupd' eltype length arr idx var)


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
                [ (Int "serving", Before "serving")
                  (Int "ticket", Before "ticket")
                  (Int "t", Intermediate (0I, "t"))
                  (Int "s", After "s") ] )


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
            [ (Array (Array (Int (), Some 320, ()), Some 240, "x"),
               Some <| aupd (Array (Int (), Some 320, ())) (Some 240) (AVar (Reg "x"))
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
               Some <| aupd (Int()) (Some 320) (AVar (Reg "y"))
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
               Some (Int (IInt 3L)))
              (Int
                (IIdx
                    (Int (),
                     Some 320,
                     AVar (Reg "y"),
                     (IVar (Reg "j")))),
               Some (Int (IInt 4L))) ]

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
                 [ dar *<- d6upd (Int d6)
                   xar *<- x3upd (Int (IInt 2L)) ],
                 [ dar *<- d6upd (Int x3)
                   xar *<- x3upd (Int x3) ])
            ]
            [ Branch
                (iEq x3 d6,
                 [ Int x3 *<- Int (IInt 2L)
                   Int d6 *<- Int d6 ],
                 [ Int x3 *<- Int x3
                   Int d6 *<- Int x3 ])
            ]


let testShared =
    Map.ofList
        [ ("grid",
            Type.Array
                (Type.Array (Type.Int (), Some 320, ()),
                    Some 240,
                    ()))
          ("test", Type.Bool ()) ]

let testShared2 =
    Map.ofList
        [ ("foo", Type.Array (Type.Bool (), Some 10, ())) ]

let testThread =
    Map.ofList
        [ ("x", Type.Int ())
          ("y", Type.Int ()) ]


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
            [ [ havoc (Int (siVar "s")) ] ]

    [<Test>]
    let ``lone assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "t")
                  iEq (siAfter "t") (siBefore "t") ])
            [ [ Int (siVar "s") *<- Int (siVar "t") ] ]

    [<Test>]
    let ``unchained assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siBefore "t")
                  iEq (siAfter "t") (siBefore "t")
                  iEq (siInter 0I "s") (siBefore "serving") ])
            [ [ Int (siVar "s") *<- Int (siVar "serving") ]
              [ Int (siVar "s") *<- Int (siVar "t") ]  ]

    [<Test>]
    let ``chained assigns are translated properly`` () =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
            (BAnd
                [ iEq (siAfter "serving") (siBefore "serving")
                  iEq (siAfter "ticket") (siBefore "ticket")
                  iEq (siAfter "s") (siInter 0I "t")
                  iEq (siAfter "t") (siInter 0I "t")
                  iEq (siInter 0I "t") (siBefore "serving") ])
            [ [ Int (siVar "t") *<- Int (siVar "serving") ]
              [ Int (siVar "s") *<- Int (siVar "t") ] ]

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
            [ [ Int (siVar "t") *<- Int (siVar "serving") ]
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
                     [ Int (siVar "t") *<- Int (siVar "serving") ],
                     [ Int (siVar "t") *<- Int (siVar "ticket") ]) ] ]

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
            [ [ Int (siVar "t") *<- Int (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ Int (siVar "t") *<- Int (mkAdd2 (siVar "t") (IInt 1L)) ]
              [ Int (siVar "t") *<- Int (mkAdd2 (siVar "t") (IInt 1L)) ] ]

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
            [ [ Int (siVar "t") *<- Int (mkAdd2 (siVar "t") (IInt 1L))
                Int (siVar "s") *<- Int (mkSub2 (siVar "s") (IInt 1L)) ]
              [ Int (siVar "t") *<- Int (mkAdd2 (siVar "t") (IInt 1L))
                Int (siVar "s") *<- Int (mkSub2 (siVar "s") (IInt 1L)) ]
              [ Int (siVar "t") *<- Int (mkAdd2 (siVar "t") (IInt 1L))
                Int (siVar "s") *<- Int (mkSub2 (siVar "s") (IInt 1L)) ] ]

    [<Test>]
    let ``arrays are normalised and translated properly`` () =
        check testShared testThread
            (BAnd
                [ iEq (siAfter "x") (siBefore "x")
                  iEq (siAfter "y") (siBefore "y")
                  bEq (sbAfter "test") (sbBefore "test")
                  BEq
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
                                (IInt 1L)))) ] )
            [ [ Expr.Int
                   (IIdx
                       (Int (),
                        Some 320,
                        AIdx
                           (Array (Int (), Some 320, ()),
                            Some 240,
                            AVar (Reg "grid"),
                            IVar (Reg "x")),
                        IVar (Reg "y")))
                *<- Expr.Int
                        (mkAdd2
                            (IIdx
                                (Int (),
                                 Some 320,
                                 AIdx
                                    (Array (Int (), Some 320, ()),
                                     Some 240,
                                     AVar (Reg "grid"),
                                     (siVar "x")),
                                 (siVar "y")))
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
    let ``Semantically translate <%{foo(#1)}(serving)[t]> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ SymC
                    { Symbol =
                        { Sentence = [ SymString "foo("; SymParamRef 1; SymString ")" ]
                          Args = [ Int (siVar "serving") ] }
                      Working = Set.singleton (Int "t") } ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "serving") (siBefore "serving")
                BVar (
                    sym [ SymString "foo("; SymParamRef 1; SymString ")" ]
                        [ Int (siBefore "serving") ]
                )
            ])

    [<Test>]
    let ``Semantically translate <serving++> using the ticket lock model``() =
        check ticketLockModel.SharedVars ticketLockModel.ThreadVars
              [ command "!I++" [ Int (siVar "serving") ] [ Expr.Int <| siVar "serving" ] ]
        <| Some (Set.ofList
            [
                iEq (siAfter "s") (siBefore "s")
                iEq (siAfter "t") (siBefore "t")
                iEq (siAfter "ticket") (siBefore "ticket")
                iEq (siAfter "serving") (mkAdd2 (siBefore "serving") (IInt 1L))
            ])
