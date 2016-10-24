/// <summary>
///     Part of the Starling tool that flattens terms, adding in globals.
/// </summary>
module Starling.Tests.Flattener

open Starling.Collections
open Starling.Flattener
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic

/// <summary>
///     Tests for <c>Flattener</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Chessie.ErrorHandling
    open Starling.Utils.Testing

    /// <summary>
    ///     The shared variables environment used in the tests.
    /// </summary>
    let svars : VarMap =
        returnOrFail <| makeVarMap
            [ TypedVar.Int "serving"
              TypedVar.Int "ticket" ]

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
             | TypedVar.Int x -> x |> siBefore |> Expr.Int
             | TypedVar.Bool x -> x |> sbBefore |> Expr.Bool
             | TypedVar.Array (eltype, length, x) ->
                Expr.Array (eltype, length, ARVar (Reg (Before x))))
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
                    [ Int "serving"
                      Int "ticket"
                      Int "t" ] )
                (flattenDView
                    svarSeq
                    [ iterated (dfunc "holdLock" []) None
                      iterated (dfunc "holdTick" [ Int "t" ]) None ])

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
                    [ Expr.Int (siBefore "serving")
                      Expr.Int (siBefore "ticket")
                      Expr.Int (siBefore "t") ] )
                (flattenOView
                    svarExprSeq
                    [ smvfunc "holdLock" []
                      smvfunc "holdTick" [ Expr.Int (siBefore "t") ]])
