/// <summary>
///     Tests for <c>Flattener</c>.
/// </summary>
module Starling.Tests.Flattener

open Chessie.ErrorHandling
open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.Collections
open Starling.Flattener
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic

/// <summary>
///     The shared variables environment used in the tests.
/// </summary>
let svars : VarMap =
    returnOrFail <| VarMap.ofTypedVarSeq
        [ TypedVar.Int (normalRec, "serving")
          TypedVar.Int (normalRec, "ticket") ]

/// <summary>
///     The globals environment as a typed variable sequence.
/// </summary>
let svarSeq : TypedVar seq =
    Seq.map (fun (n, t) -> withType t n) (Map.toSeq svars)

/// <summary>
///     The globals environment as a pre-state expression sequence.
/// </summary>
let svarExprSeq : Expr<Sym<MarkedVar>> seq =
    Seq.map
        (function
            | TypedVar.Int (t, x) -> Expr.Int (t, siBefore x)
            | TypedVar.Bool (t, x) -> Expr.Bool (t, sbBefore x)
            | TypedVar.Array (t, x) -> Expr.Array (t, AVar (Reg (Before x))))
        svarSeq

/// <summary>
///     Tests for the flattened func name mangler.
/// </summary>
module NamingTests =
    [<Test>]
    let ``Encode name of view 'foo() * bar_baz()' as 'v_foo_bar__bazo'`` () =
        assertEqual
            "v_foo_bar__baz"
            (genFlatFuncSeqName [ regFunc "foo" []; regFunc "bar_baz" [] ])

    [<Test>]
    let ``Encode name of view '' as 'emp'`` () =
        assertEqual
            "emp"
            (genFlatFuncSeqName ([] : SMVFunc list))

/// <summary>
///     Tests for the defining-view flattener.
/// </summary>
module DViewFlattening =
    [<Test>]
    let ``Convert non-iterated DView to defining func`` () =
        assertEqual
            (func "v_holdLock_holdTick"
                [ TypedVar.Int (normalRec, "serving")
                  TypedVar.Int (normalRec, "ticket")
                  TypedVar.Int (normalRec, "t") ]
                Erased)
            (flattenDView
                svarSeq
                [ iterated (regFunc "holdLock" []) None
                  iterated (regFunc "holdTick" [ TypedVar.Int (normalRec, "t") ]) None ])

    // TODO(CaptainHayashi): iterated DView tests
    //   (that, or move the iterator lowering to IterLower where it belongs)

/// <summary>
///     Tests for the main view flattener.
/// </summary>
module OViewFlattening =
    [<Test>]
    let ``Convert arity-2 OView to func`` () =
        assertEqual
            (func "v_holdLock_holdTick"
                [ normalIntExpr (siBefore "serving")
                  normalIntExpr (siBefore "ticket")
                  normalIntExpr (siBefore "t") ]
                Erased)
            (flattenOView
                svarExprSeq
                [ regFunc "holdLock" []
                  regFunc "holdTick" [ normalIntExpr (siBefore "t") ]])

/// <summary>
///     Tests for the iterator flattener.
/// </summary>
module TestIterFlatten =
    open Starling.Flattener.Iter
    open Starling.Core.Definer
    open Starling.Core.GuardedView
    open Starling.Core.Model
    open Starling.Utils

    module TestLowerGuards =
        let protos =
            FuncDefiner.ofSeq
                [ (regFunc "f" [Bool (normalRec, "x")], { IsIterated = true; IsAnonymous = false })
                  (regFunc "g" [Bool (normalRec, "x")], { IsIterated = false; IsAnonymous = false }) ]

        [<Test>]
        let ``Drop iterated subview down to non-iterated subview`` ()=
            assertOkAndEqual
                ({ Cond = (BTrue : BoolExpr<Sym<MarkedVar>>)
                   Item = [ regFunc "f" [normalIntExpr (IInt 3L); normalBoolExpr BTrue] ] })
                (lowerIteratedSubview
                    protos
                    { Cond = BTrue
                      Item =
                        [ iterated
                            (regFunc "f" [normalBoolExpr BTrue])
                            (IInt 3L) ] })
                (printError >> Starling.Core.Pretty.printUnstyled)

        [<Test>]
        let ``Drop iterated SMVFunc down to non-iterated SMVFunc`` ()=
            assertOkAndEqual
                [ regFunc "f"
                    [ normalIntExpr (mkMul2 (IInt 2L) (siBefore "n"))
                      normalBoolExpr (sbAfter "x") ]]
                (lowerIterSMVFunc
                    protos
                    (iterated
                        (regFunc "f" [normalBoolExpr (sbAfter "x")])
                        (mkMul2 (IInt 2L) (siBefore "n"))))
                (printError >> Starling.Core.Pretty.printUnstyled)

        [<Test>]
        let ``Drop non-iterated IteratedSMVFunc's down to non-iterated SMVFunc`` ()=
            assertOkAndEqual
                [ for _ in 1..4 -> regFunc "g" [ normalBoolExpr (sbAfter "z") ]]
                (lowerIterSMVFunc
                    protos
                    (iterated
                        (regFunc "g" [normalBoolExpr (sbAfter "z")])
                        (IInt 4L)))
                (printError >> Starling.Core.Pretty.printUnstyled)
