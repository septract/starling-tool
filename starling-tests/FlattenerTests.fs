/// <summary>
///     Tests for <c>Flattener</c>.
/// </summary>
module Starling.Tests.Flattener

open Chessie.ErrorHandling
open NUnit.Framework

open Starling.Tests.TestUtils

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
            (genFlatFuncSeqName [ smvfunc "foo" []; smvfunc "bar_baz" [] ])

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
            (dfunc "v_holdLock_holdTick"
                [ TypedVar.Int (normalRec, "serving")
                  TypedVar.Int (normalRec, "ticket")
                  TypedVar.Int (normalRec, "t") ] )
            (flattenDView
                svarSeq
                [ iterated (dfunc "holdLock" []) None
                  iterated (dfunc "holdTick" [ TypedVar.Int (normalRec, "t") ]) None ])

    // TODO(CaptainHayashi): iterated DView tests
    //   (that, or move the iterator lowering to IterLower where it belongs)


/// <summary>
///     Tests for the main view flattener.
/// </summary>
module OViewFlattening =
    [<Test>]
    let ``Convert arity-2 OView to func`` () =
        assertEqual
            (smvfunc "v_holdLock_holdTick"
                [ normalIntExpr (siBefore "serving")
                  normalIntExpr (siBefore "ticket")
                  normalIntExpr (siBefore "t") ] )
            (flattenOView
                svarExprSeq
                [ smvfunc "holdLock" []
                  smvfunc "holdTick" [ normalIntExpr (siBefore "t") ]])

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
                [ (dfunc "f" [Bool (normalRec, "x")], { IsIterated = true; IsAnonymous = false })
                  (dfunc "g" [Bool (normalRec, "x")], { IsIterated = false; IsAnonymous = false }) ]

        [<Test>]
        let ``Drop iterated subview down to non-iterated subview`` ()=
            Assert.That(
                okOption <|
                lowerIteratedSubview
                    protos
                    { Cond = BTrue
                      Item =
                        [ iterated
                            (smvfunc "f" [normalBoolExpr BTrue])
                            (IInt 3L) ] },
                Is.EqualTo(
                    Some <|
                    { Cond = (BTrue : BoolExpr<Sym<MarkedVar>>)
                      Item = [ smvfunc "f" [normalIntExpr (IInt 3L); normalBoolExpr BTrue] ] }))

        [<Test>]
        let ``Drop iterated SMVFunc down to non-iterated SMVFunc`` ()=
            Assert.That(
                okOption <|
                lowerIterSMVFunc
                    protos
                    (iterated
                        (smvfunc "f" [normalBoolExpr (sbAfter "x")])
                        (mkMul2 (IInt 2L) (siBefore "n"))),
                Is.EqualTo(
                    Some <|
                    [ smvfunc "f"
                        [ normalIntExpr (mkMul2 (IInt 2L) (siBefore "n"))
                          normalBoolExpr (sbAfter "x") ]]))

        [<Test>]
        let ``Drop non-iterated IteratedSMVFunc's down to non-iterated SMVFunc`` ()=
            Assert.That(
                okOption <|
                lowerIterSMVFunc
                    protos
                    (iterated
                        (smvfunc "g" [normalBoolExpr (sbAfter "z")])
                        (IInt 4L)),
                Is.EqualTo(
                    Some <|
                    [ for x in 1..4 -> smvfunc "g" [ normalBoolExpr (sbAfter "z") ]]))
