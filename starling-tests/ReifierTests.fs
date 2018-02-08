/// <summary>
///     Tests for <c>Starling.Reifier</c>.
/// </summary>
module Starling.Tests.Reifier

open NUnit.Framework
open Starling.Tests.TestUtils
open Starling.Collections
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.TypeSystem
open Starling.Core.View
open Starling.Reifier


/// <summary>
///     Tests for powerset generation.
/// </summary>
module Powerset =
    [<Test>]
    let ``The powerset of the empty set is the set of the empty-set`` () =
        List.sort <| [[]]
        ?=?
        (List.sort <| List.ofSeq (powerset []))

    [<Test>]
    let ``The powerset of singleton is the set of empty-set and singleton`` () =
        List.sort <| [[]; [1]]
        ?=?
        (List.sort <| List.ofSeq (powerset [1]))

    [<Test>]
    let ``The powerset of a non-singleton set is calculated properly`` () =
        List.sort <| [[]; [1]; [2]; [3]; [1; 2]; [1; 3]; [2; 3]; [1; 2; 3]]
        ?=?
        (List.sort <| List.ofSeq (powerset [1; 2; 3]))


/// <summary>
///     Tests for parameter equality calculation.
/// </summary>
module ParamEqualities =
    [<Test>]
    let ``Parameter equalities on a single func are empty`` () =
        [] ?=?
        paramEqualities
            [ iteratedFunc "A"
                [ normalIntExpr (siBefore "x1"); normalIntExpr (siBefore "y1") ]
                (IInt 1L) ]

    [<Test>]
    let ``Parameter equalities on a set of nullary funcs are empty`` () =
        [] ?=?
        paramEqualities
            [ iterated (regFunc "A" []) (IInt 1L)
              iterated (regFunc "A" []) (IInt 1L) ]

    [<Test>]
    let ``Parameter equalities on parameterised funcs are correct`` () =
        [ iEq (siBefore "x1") (siBefore "x2")
          iEq (siAfter "y1") (siAfter "y2")
          bEq (sbBefore "z1") (sbBefore "z2")
          iEq (siBefore "x1") (siBefore "x3")
          iEq (siAfter "y1") (siAfter "y3")
          bEq (sbBefore "z1") (sbBefore "z3")
          iEq (siBefore "x1") (siBefore "x4")
          iEq (siAfter "y1") (siAfter "y4")
          bEq (sbBefore "z1") (sbBefore "z4") ] ?=?
        paramEqualities
            [ iteratedFunc "A"
                [ normalIntExpr (siBefore "x1"); normalIntExpr (siAfter "y1"); normalBoolExpr (sbBefore "z1") ]
                (IInt 1L)
              iteratedFunc "A"
                [ normalIntExpr (siBefore "x2"); normalIntExpr (siAfter "y2"); normalBoolExpr (sbBefore "z2") ]
                (IInt 10L)
              iteratedFunc "A"
                [ normalIntExpr (siBefore "x3"); normalIntExpr (siAfter "y3"); normalBoolExpr (sbBefore "z3") ]
                (siBefore "i")
              iteratedFunc "A"
                [ normalIntExpr (siBefore "x4"); normalIntExpr (siAfter "y4"); normalBoolExpr (sbBefore "z4") ]
                (IMul [ siAfter "j"; IInt 6L ]) ]

/// <summary>
///     Tests for view preprocessing.
/// </summary>
module ViewPreprocess =
    open Starling.Collections
    open Starling.Core.GuardedView
    open Starling.Core.Model

    /// <summary>
    ///     View prototypes for the following tests.
    /// </summary>
    let protos : FuncDefiner<ProtoInfo> =
        FuncDefiner.ofSeq
            [ (regFunc "A" [ normalIntVar "x"; normalIntVar "y"; normalBoolVar "z" ],
               { IsIterated = true ; IsAnonymous = false })
              (regFunc "B" [ normalIntVar "n" ],
               { IsIterated = false ; IsAnonymous = false }) ]

    [<Test>]
    let ``the empty view preprocesses to the empty view`` () =
        [] ?=?
        preprocessView protos (Multiset.empty)

    [<Test>]
    let ``two distinct non-iterated views preprocess without change`` () =
        [ iteratedGFunc
            (sbBefore "G2")
            "B"
            [ normalIntExpr (siAfter "n2") ]
            (siAfter "k")
          iteratedGFunc
            (sbBefore "G1")
            "B"
            [ normalIntExpr (siBefore "n1") ]
            (IInt 5L) ]
        ?=?
        preprocessView protos
            (Multiset.ofFlatList
                [ iteratedGFunc
                    (sbBefore "G1")
                    "B"
                    [ normalIntExpr (siBefore "n1") ]
                    (IInt 5L)
                  iteratedGFunc
                    (sbBefore "G2")
                    "B"
                    [ normalIntExpr (siAfter "n2") ]
                    (siAfter "k") ])

    [<Test>]
    let ``two distinct iterated views preprocess without change`` () =
        [ iteratedGFunc
            (mkAnd [ sbBefore "G2"; sbBefore "G1"
                     iEq (siAfter "x2") (siBefore "x1")
                     iEq (siAfter "y2") (siBefore "y1")
                     bEq (sbAfter "z2") (sbBefore "z1") ])
            "A"
            [ normalIntExpr (siAfter "x2"); normalIntExpr (siAfter "y2"); normalBoolExpr (sbAfter "z2") ]
            (mkAdd2 (siAfter "k") (IInt 5L))
          iteratedGFunc
            (sbBefore "G1")
            "A"
            [ normalIntExpr (siBefore "x1"); normalIntExpr (siBefore "y1"); normalBoolExpr (sbBefore "z1") ]
            (IInt 5L)
          iteratedGFunc
            (sbBefore "G2")
            "A"
            [ normalIntExpr (siAfter "x2"); normalIntExpr (siAfter "y2"); normalBoolExpr (sbAfter "z2") ]
            (siAfter "k") ]
        ?=?
        preprocessView protos
            (Multiset.ofFlatList
                [ iteratedGFunc
                    (sbBefore "G2")
                    "A"
                    [ normalIntExpr (siAfter "x2"); normalIntExpr (siAfter "y2"); normalBoolExpr (sbAfter "z2") ]
                    (siAfter "k")
                  iteratedGFunc
                    (sbBefore "G1")
                    "A"
                    [ normalIntExpr (siBefore "x1"); normalIntExpr (siBefore "y1"); normalBoolExpr (sbBefore "z1") ]
                    (IInt 5L) ])
