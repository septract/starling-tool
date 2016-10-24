/// <summary>
///     Tests for <c>Starling.Tests.Modeller</c>.
/// </summary>
module Starling.Tests.Modeller

open NUnit.Framework
open Starling
open Starling.Utils.Testing
open Starling.Collections
open Starling.Core
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Lang.AST
open Starling.Core.Model
open Starling.Lang.Modeller
open Starling.Tests.Studies

let ticketLockProtos: FuncDefiner<ProtoInfo> =
    FuncDefiner.ofSeq
        [ (func "holdLock" [], { IsIterated = false ; IsAnonymous = false })
          (func "holdTick" [ Int "t" ], { IsIterated = false ; IsAnonymous = false }) ]

let environ =
    Map.ofList [ ("foo", Type.Int ())
                 ("bar", Type.Int ())
                 ("baz", Type.Bool ())
                 ("emp", Type.Bool ()) ]

let shared =
    Map.ofList [ ("x", Type.Int ())
                 ("y", Type.Bool ()) ]

let context =
    { ViewProtos = ticketLockProtos
      SharedVars = Map.empty
      ThreadVars = environ }

let sharedContext =
    { ViewProtos = ticketLockProtos
      SharedVars = shared
      ThreadVars = environ }

module ViewPass =
    let check (view : View) (expectedCView : CView) =
        let actualCView = okOption <| modelCView context view
        AssertAreEqual(Some expectedCView, actualCView)

    [<Test>]
    let ``check emp`` () =
        check View.Unit Multiset.empty

    [<Test>]
    let ``test correct func``() =
        check
            (View.Func <| afunc "holdLock" [])
            (Multiset.singleton
                (iterated
                    (CFunc.Func (vfunc "holdLock" []))
                    None))

module ViewFail =
    let check (view : View) (expectedFailures : ViewError list) =
        let actualErrors = failOption <| modelCView context view
        AssertAreEqual(Some expectedFailures, actualErrors)

    [<Test>]
    let ``test unknown func``() =
        check
            (View.Func <| afunc "badfunc" [])
            ([ NoSuchView "badfunc" ])

    [<Test>]
    let ``test missing parameter``() =
        check
            (View.Func <| afunc "holdTick" [])
            ([ LookupError ("holdTick", CountMismatch(0, 1)) ])

    [<Test>]
    let ``test bad parameter type``() =
        check
          (View.Func <| afunc "holdTick" [freshNode Expression'.True])
          ([ LookupError
               ( "holdTick",
                 Error.TypeMismatch
                   (Int "t", Type.Bool ())) ])

module ArithmeticExprs =
    let check (ast : Expression) (expectedExpr : IntExpr<Sym<Var>>) =
        let actualIntExpr = okOption <| modelIntExpr environ id ast
        AssertAreEqual(Some expectedExpr, actualIntExpr)

    [<Test>]
    let ``test modelling (1 * 3) % 2`` ()=
        check
            (freshNode <| BopExpr( Mod,
                                   freshNode <| BopExpr(Mul, freshNode (Num 1L), freshNode (Num 3L)),
                                   freshNode (Num 2L) ))
            // TODO (CaptainHayashi): this shouldn't be optimised?
            (IInt 1L)

    [<Test>]
    let ``test modelling (1 * 2) + 3`` ()=
        check
            (freshNode <| BopExpr( Add,
                                   freshNode <| BopExpr(Mul, freshNode (Num 1L), freshNode (Num 2L)),
                                   freshNode (Num 3L) ))
            // TODO (CaptainHayashi): this shouldn't be optimised?
            (IInt 5L)

module BooleanExprs =
    let check (ast : Expression) (expectedExpr : BoolExpr<Sym<Var>>) =
        let actualBoolExpr = okOption <| modelBoolExpr environ id ast
        AssertAreEqual(Some expectedExpr, actualBoolExpr)

    [<Test>]
    let ``model (true || true) && false`` () =
        check
            (freshNode <| BopExpr(And, freshNode <| BopExpr(Or, freshNode True, freshNode True), freshNode False))
            (BFalse : BoolExpr<Sym<Var>>)

module VarLists =
    let checkFail (vars : TypedVar list) (expectedErrs : VarMapError list) =
        let varmap = failOption <| VarMap.ofTypedVarSeq vars
        AssertAreEqual(Some expectedErrs, varmap)

    let checkPass (vars : TypedVar list) (expectedMap : Map<string, CTyped<unit>>) =
        let varmap = okOption <| VarMap.ofTypedVarSeq vars
        AssertAreEqual(Some expectedMap, varmap)

    [<Test>]
    let ``valid empty list makes var map`` () =
        checkPass
            []
            Map.empty

    [<Test>]
    let ``valid singleton list makes var map`` () =
        checkPass
            [ Int "bar" ]
            (Map.ofList [ ("bar", Int ()) ])

    [<Test>]
    let ``valid multi list makes var map`` () =
        checkPass
            [ Int "bar"; Bool "baz" ]
            (Map.ofList [ ("bar", Int ())
                          ("baz", Bool ()) ])

    [<Test>]
    let ``duplicate vars of same type fail in VarMap.ofTypedVarSeq`` () =
        checkFail
            ([ Bool "foo"
               Bool "foo" ])
            ([ VarMapError.Duplicate "foo" ])

    [<Test>]
    let ``duplicate var with different type fails in VarMap.ofTypedVarSeq`` () =
        checkFail
            ([ Bool "foo"
               Int  "foo" ])
            ([ VarMapError.Duplicate "foo" ])

module Atomics =
    let check (ast : Atomic) (cmd : PrimCommand) =
        let actualCmd = okOption <| modelAtomic sharedContext ast
        AssertAreEqual(Some cmd, actualCmd)

    [<Test>]
    let ``model integer load primitive <foo = x++>`` ()=
        let ast = freshNode (Fetch((LVIdent "foo"), freshNode (LV(LVIdent "x")), Increment))
        check
            ast
            <| command' "!ILoad++"
                ast
                [ Int "foo"; Int "x" ]
                [ "x" |> siBefore |> SMExpr.Int ]

module CommandAxioms =
    let check (c : Command<ViewExpr<View>>) (cmd : ModellerPartCmd) =
        let actualCmd = okOption <| modelCommand sharedContext c
        AssertAreEqual(Some cmd, actualCmd)

    let prim (atom : Atomic) : Command<ViewExpr<View>> =
        freshNode
        <| Command'.Prim { PreAssigns = []
                           Atomics = [ atom ]
                           PostAssigns = [] }

    [<Test>]
    let ``modelling command <foo = x++> passes`` () =
        let ast = freshNode (Fetch((LVIdent "foo"), freshNode (LV(LVIdent "x")), Increment))
        check
            (prim <| ast)
            <| Prim ([ command' "!ILoad++"
                        ast
                        [ Int "foo"; Int "x" ]
                        [ "x" |> siBefore |> SMExpr.Int ] ])



module ViewDefs =
    let check (search : int option) (defs : ViewDefiner<BoolExpr<Sym<Var>> option>) expected =
        let viewdef = addSearchDefs ticketLockProtos search defs
        let actual = Set.ofSeq <| ViewDefiner.toSeq viewdef
        AssertAreEqual(expected, actual)

    /// Type-constraining builder for viewdef sets.
    let viewDefSet
      (vs : (View.Types.DView * BoolExpr<Sym<Var>> option) seq)
      : Set<View.Types.DView * BoolExpr<Sym<Var>> option> =
        Set.ofSeq vs

    /// Type-constraining builder for indefinite viewdef sets.
    let indefinites (vs : View.Types.DView seq)
      : Set<View.Types.DView * BoolExpr<Sym<Var>> option> =
        vs
        |> Seq.map (fun v -> (v, None))
        |> viewDefSet

    [<Test>]
    let ``Search for no viewdefs does not change empty viewdef set``() =
        check None []
            (indefinites [])

    [<Test>]
    let ``Search for no viewdef does not alter full viewdef set``() =
        check None ticketLockViewDefs
            (viewDefSet ticketLockViewDefs)

    [<Test>]
    let ``search for size-0 viewdefs adds emp to empty``() =
        check (Some 0) []
            (indefinites [ [] ])

    [<Test>]
    let ``search for size-0 viewdefs does not change full``() =
        check (Some 0) ticketLockViewDefs
            (viewDefSet ticketLockViewDefs)

    [<Test>]
    let ``Search for size-1 viewdefs yields viewdefs for emp and single view protos``() =
        check (Some 1) []
            (indefinites
                [ []
                  [ iterated (func "holdLock" []) None ]
                  [ iterated (func "holdTick" [ Int "t0" ]) None ] ])

    [<Test>]
    let ``Search for size-2 viewdefs yields viewdefs up to size 2``() =
        check (Some 2) []
            (indefinites
                [ []
                  [ iterated (func "holdLock" []) None ]
                  [ iterated (func "holdLock" []) None
                    iterated (func "holdLock" []) None ]
                  [ iterated (func "holdLock" []) None
                    iterated (func "holdTick" [ Int "t0" ]) None ]
                  [ iterated (func "holdTick" [ Int "t0" ]) None ]
                  [ iterated (func "holdTick" [ Int "t0" ]) None
                    iterated (func "holdTick" [ Int "t1" ]) None ] ] )
