/// <summary>
///     Tests for <c>Starling.Core.Instantiate</c>.
/// </summary>
module Starling.Tests.Instantiate

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Utils.Testing
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic
open Starling.Core.Instantiate
open Starling.Core.Pretty
open Starling.Core.Traversal
open Starling.Core.Instantiate.Pretty


/// Tests for the func instantiation functions.
module FuncInstantiate =
    /// Environment of test funcs.
    let TestFuncs =
        [ (dfunc "foo" [],
           iEq (IInt 5L : SVIntExpr) (IInt 6L))
          (dfunc "bar" [ Int (normalRec, "quux") ],
           iEq (siVar "quux") (IInt 6L))
          (dfunc "baz" [ Int (normalRec, "quux") ; Bool (normalRec, "flop") ],
           BAnd [sbVar "flop"; BGt (normalInt (siVar "quux"), normalInt (siVar "quux"))]) ]

    let checkInstantiate expected case : unit =
        assertOkAndEqual
            expected
            (instantiate TestFuncs case)
            (printError >> printUnstyled)

    let testInstantiateFail =
        instantiate TestFuncs >> failOption

    let none : Option<BoolExpr<Sym<MarkedVar>>> = None

    [<Test>]
    let ``Instantiate undefined func`` () =
        checkInstantiate
            None
            (smvfunc "nope" [])

    [<Test>]
    let ``Instantiate func with no arguments``() =
        checkInstantiate
            (Some (iEq (IInt 5L : SMIntExpr) (IInt 6L : SMIntExpr)))
            (smvfunc "foo" [])

    [<Test>]
    let ``Instantiate func with one integer argument``() =
        checkInstantiate
            (Some (iEq (IInt 101L) (IInt 6L : SMIntExpr)))
            (smvfunc "bar" [ normalIntExpr (IInt 101L) ])

    [<Test>]
    let ``Instantiate func with two arguments of different types``() =
        checkInstantiate
            (Some (BAnd [ BTrue; BGt (normalInt (siAfter "burble"),
                                      normalInt (siAfter "burble")) ]))
            (smvfunc "baz"
                [ normalIntExpr (siAfter "burble")
                  normalBoolExpr BTrue ])

    [<Test>]
    let ``Instantiate func with too many arguments``() =
        Some
            [ Traversal
                (Inner
                    (BadFuncLookup
                        (smvfunc "foo" [ normalIntExpr (IInt 101L) ],
                         CountMismatch(1, 0)))) ]
        ?=? testInstantiateFail (smvfunc "foo" [ normalIntExpr (IInt 101L) ])

    [<Test>]
    let ``Instantiate func with too few arguments``() =
        Some
            [ Traversal
                (Inner
                    (BadFuncLookup
                        (smvfunc "bar" [],
                         CountMismatch(0, 1)))) ]
        ?=? testInstantiateFail (smvfunc "bar" [])

    [<Test>]
    let ``Instantiate func with two arguments of incorrect types``() =
        Some
            [ Traversal
                (Inner
                    (BadFuncLookup
                        (smvfunc "baz"
                            [ normalBoolExpr BTrue
                              normalIntExpr (siAfter "burble") ],
                         TypeMismatch (Int (normalRec, "quux"), Bool (normalRec, ())))))
              Traversal
                (Inner
                    (BadFuncLookup
                        (smvfunc "baz"
                            [ normalBoolExpr BTrue
                              normalIntExpr (siAfter "burble") ],
                         TypeMismatch (Bool (normalRec, "flop"), Int (normalRec, ()))))) ]
        ?=?
            testInstantiateFail
                (smvfunc "baz"
                    [ normalBoolExpr BTrue
                      normalIntExpr (siAfter "burble") ])
