/// <summary>
///     Tests for <c>Starling.Tests.Modeller</c>.
/// </summary>
module Starling.Tests.Modeller

open NUnit.Framework
open Starling
open Starling.Tests.TestUtils
open Starling.Collections
open Starling.Core
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.GuardedView
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Lang.AST
open Starling.Lang.Desugar
open Starling.Core.Model
open Starling.Lang.Modeller
open Starling.Tests.Studies

let ticketLockProtos: FuncDefiner<ProtoInfo> =
    FuncDefiner.ofSeq
        [ (func "holdLock" [], { IsIterated = false ; IsAnonymous = false })
          (func "holdTick" [ Int (normalRec, "t") ], { IsIterated = false ; IsAnonymous = false }) ]

let environ =
    Map.ofList [ ("foo", Type.Int (normalRec, ()))
                 ("bar", Type.Int (normalRec, ()))
                 ("baz", Type.Bool (normalRec, ()))
                 ("emp", Type.Bool (normalRec, ()))
                 // Subtyped variables
                 ("lnode", Type.Int ({ PrimSubtype = Named "Node" }, ()))
                 // Multi-dimensional arrays
                 ("grid",
                  mkArrayType
                    (mkArrayType (Type.Int (normalRec, ())) (Some 320))
                    (Some 240)) ]

let shared =
    Map.ofList [ ("nums", mkArrayType (Type.Int (normalRec, ())) (Some 10))
                 ("x", Type.Int (normalRec, ()))
                 ("y", Type.Bool (normalRec, ()))
                 ("node", Type.Int ({ PrimSubtype = Named "Node" }, ())) ]

let context =
    { ViewProtos = ticketLockProtos
      Env = Env.env environ Map.empty }

let sharedContext =
    { ViewProtos = ticketLockProtos
      Env = Env.env environ shared }


module ViewPass =
    let check
      (expected : IteratedGView<Sym<Var>>)
      (view : DesugaredGView)
      : unit =
        assertOkAndEqual
            expected
            (modelView context view)
            (Starling.Core.Pretty.printUnstyled <<
                Starling.Lang.Modeller.Pretty.printViewError)


    [<Test>]
    let ``check emp`` () =
        check Multiset.empty []

    [<Test>]
    let ``test correct func``() =
        check
            (Multiset.singleton
                (iterated
                    (gfunc BTrue "holdLock" [])
                    (IInt 1L)))
            [ ( freshNode True, afunc "holdLock" [] ) ]


module ViewFail =
    let check (expected : ViewError list) (view : DesugaredGView) : unit =
        assertEqual (Some expected) (failOption (modelView context view))

    [<Test>]
    let ``test unknown func`` () =
        check
            [ NoSuchView "badfunc" ]
            [ (freshNode True, afunc "badfunc" []) ]

    [<Test>]
    let ``test missing parameter`` () =
        check
            [ LookupError ("holdTick", CountMismatch(0, 1)) ]
            [ (freshNode True, afunc "holdTick" []) ]

    [<Test>]
    let ``test bad parameter type`` () =
        check
          [ LookupError
               ( "holdTick",
                 Error.TypeMismatch
                   (Int (normalRec, "t"), Type.Bool (indefRec, ()))) ]
          [ (freshNode True, afunc "holdTick" [freshNode Expression'.True]) ]

    [<Test>]
    let ``test bad parameter subtype`` () =
        check
          [ LookupError
               ( "holdTick",
                 Error.TypeMismatch
                   (normalIntVar "t", Type.Int ({ PrimSubtype = Named "Node" }, ()))) ]
          [ (freshNode True, afunc "holdTick" [freshNode (Identifier "lnode")]) ]


module ArithmeticExprs =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Lang.Modeller.Pretty

    let check (env : VarMap) (ast : Expression) (expectedExpr : TypedIntExpr<Sym<Var>>) =
        let e = Env.env environ env
        assertOkAndEqual
            expectedExpr
            (modelIntExpr e Shared id ast)
            (printExprError >> printUnstyled)

    let checkFail (env : VarMap) (ast : Expression) (expectedErrors : ExprError list) =
        let e = Env.env environ env
        assertFail
            expectedErrors
            (modelIntExpr e Shared id ast)
            (stripTypeRec >> printIntExpr (printSym printVar) >> printUnstyled)

    [<Test>]
    let ``test modelling (1 * 3) % 2`` ()=
        check environ
            (freshNode <| BopExpr( Mod,
                                   freshNode <| BopExpr(Mul, freshNode (Num 1L), freshNode (Num 3L)),
                                   freshNode (Num 2L) ))
            // TODO (CaptainHayashi): this shouldn't be optimised?
            (indefInt (IInt 1L))

    [<Test>]
    let ``test modelling (1 * 2) + 3`` ()=
        check environ
            (freshNode <| BopExpr( Add,
                                   freshNode <| BopExpr(Mul, freshNode (Num 1L), freshNode (Num 2L)),
                                   freshNode (Num 3L) ))
            // TODO (CaptainHayashi): this shouldn't be optimised?
            (indefInt (IInt 5L))

    [<Test>]
    let ``test modelling (foo + bar) succeeds with type 'int'`` () =
        // These two are of different subtypes.
        check environ
            (freshNode <| BopExpr( Add,
                                   freshNode (Identifier "foo"),
                                   freshNode (Identifier "bar")))
            (normalInt (mkAdd2 (siVar "foo") (siVar "bar")))

    [<Test>]
    let ``test modelling (foo + 3) succeeds with type 'int'`` () =
        // These two are of different subtypes.
        check environ
            (freshNode <| BopExpr( Add,
                                   freshNode (Identifier "foo"),
                                   freshNode (Num 3L)))
            (normalInt (mkAdd2 (siVar "foo") (IInt 3L)))

    [<Test>]
    let ``test modelling (lnode + 3) succeeds with type 'Node'`` () =
        // These two are of different subtypes.
        check environ
            (freshNode <| BopExpr( Add,
                                   freshNode (Identifier "lnode"),
                                   freshNode (Num 3L)))
            (mkTypedSub { PrimSubtype = Named "Node"} (mkAdd2 (siVar "lnode") (IInt 3L)))

    [<Test>]
    let ``test modelling (foo + lnode) fails`` () =
        // These two are of different subtypes.
        checkFail environ
            (freshNode <| BopExpr( Add,
                                   freshNode (Identifier "foo"),
                                   freshNode (Identifier "lnode")))
            // This shouldn't really be order-sensitive.
            [ exprTypeMismatch
                (Exact (Int (normalRec, ())))
                (Exact (Int ({ PrimSubtype = Named "Node" }, ()))) ]

    [<Test>]
    let ``test modelling shared array access nums[foo + 1]`` ()=
        check shared
            (freshNode <| ArraySubscript
                (freshNode (Identifier "nums"),
                 freshNode <| BopExpr
                    (Add,
                     freshNode (Identifier "foo"),
                     freshNode (Num 3L))))
            (normalInt
                (IIdx
                    (mkTypedSub
                        (mkArrayTypeRec (Int (normalRec, ())) (Some 10))
                        (AVar (Reg "nums")),
                     mkAdd2 (IVar (Reg "foo")) (IInt 3L))))

    [<Test>]
    let ``test modelling shared array access nums[lnode + 1] fails`` ()=
        // We shouldn't be able to index arrays by things that aren't int.
        checkFail shared
            (freshNode <| ArraySubscript
                (freshNode (Identifier "nums"),
                 freshNode <| BopExpr
                    (Add,
                     freshNode (Identifier "lnode"),
                     freshNode (Num 3L))))
            [ exprTypeMismatch
                (Exact (Int (normalRec, ())))
                (Exact (Int ({ PrimSubtype = Named "Node" }, ()))) ]

    [<Test>]
    let ``test modelling local array access grid[x][y]`` () =
        check environ
            (freshNode <| ArraySubscript
                (freshNode <| ArraySubscript
                     (freshNode (Identifier "grid"),
                      freshNode (Identifier "foo")),
                 freshNode (Identifier "bar")))
            (normalInt
                (IIdx
                    (mkTypedSub
                        (mkArrayTypeRec (Int (normalRec, ())) (Some 320))
                        (AIdx
                            (mkTypedSub
                                (mkArrayTypeRec
                                    (mkArrayType (Int (normalRec, ())) (Some 320))
                                    (Some 240))
                                (AVar (Reg "grid")),
                            (IVar (Reg "foo")))),
                      IVar (Reg "bar"))))


module BooleanExprs =
    let check (env : VarMap) (ast : Expression) (expectedExpr : TypedBoolExpr<Sym<Var>>) =
        let e = Env.env environ env
        let actualBoolExpr = okOption <| modelBoolExpr e Shared id ast
        AssertAreEqual(Some expectedExpr, actualBoolExpr)

    [<Test>]
    let ``model (true || true) && false`` () =
        check environ
            (freshNode <| BopExpr(And, freshNode <| BopExpr(Or, freshNode True, freshNode True), freshNode False))
            (indefBool BFalse)


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
            [ Int (normalRec, "bar") ]
            (Map.ofList [ ("bar", Int (normalRec, ())) ])

    [<Test>]
    let ``valid multi list makes var map`` () =
        checkPass
            [ Int (normalRec, "bar"); Bool (normalRec, "baz") ]
            (Map.ofList [ ("bar", Int (normalRec, ()))
                          ("baz", Bool (normalRec, ())) ])

    [<Test>]
    let ``duplicate vars of same type fail in VarMap.ofTypedVarSeq`` () =
        checkFail
            ([ Bool (normalRec, "foo")
               Bool (normalRec, "foo") ])
            ([ VarMapError.Duplicate "foo" ])

    [<Test>]
    let ``duplicate var with different type fails in VarMap.ofTypedVarSeq`` () =
        checkFail
            ([ Bool (normalRec, "foo")
               Int  (normalRec,  "foo") ])
            ([ VarMapError.Duplicate "foo" ])


let aprim (p : Prim') : DesugaredAtomic = DAPrim (freshNode p)

module Atomics =
    open Starling.Core.Pretty
    open Starling.Lang.Modeller.Pretty
    let check (ast : DesugaredAtomic) (cmd : PrimCommand list) : unit =
        assertOkAndEqual
            cmd
            (modelAtomic sharedContext.Env ast)
            (printPrimError >> printUnstyled)

    [<Test>]
    let ``model integer load primitive <foo = x++>`` ()=
        let ast =
            aprim (Fetch(freshNode (Identifier "foo"), freshNode (Identifier "x"), Increment))

        check
            ast
            [ normalIntExpr (siVar "foo") *<- normalIntExpr (siVar "x")
              normalIntExpr (siVar "x") *<- normalIntExpr (mkInc (siVar "x")) ]

    [<Test>]
    let ``model Boolean load primitive <baz = y>`` ()=
        let ast =
            aprim (Fetch(freshNode (Identifier "baz"), freshNode (Identifier "y"), Direct))
        check
            ast
            [ normalBoolExpr (sbVar "baz") *<- normalBoolExpr (sbVar "y") ]

    [<Test>]
    let ``model integer increment on local variable`` () =
        let ast =
            aprim (Postfix(freshNode (Identifier "x"), Increment))
        check
            ast
            [ normalIntExpr (siVar "x") *<- normalIntExpr (mkInc (siVar "x")) ]

    [<Test>]
    let ``model integer decrement on local variable`` () =
        let ast = aprim (Postfix(freshNode (Identifier "x"), Decrement))
        check
            ast
            [ normalIntExpr (siVar "x") *<- normalIntExpr (mkDec (siVar "x")) ]

    [<Test>]
    let ``model integer increment on shared variable`` () =
        let ast = aprim (Postfix(freshNode (Identifier "bar"), Increment))
        check
            ast
            [ normalIntExpr (siVar "bar") *<- normalIntExpr (mkInc (siVar "bar")) ]

    [<Test>]
    let ``model integer decrement on shared variable`` ()=
        let ast = aprim (Postfix(freshNode (Identifier "bar"), Decrement))
        check
            ast
            [ normalIntExpr (siVar "bar") *<- normalIntExpr (mkDec (siVar "bar")) ]

    [<Test>]
    let ``model Boolean atomic assign from shared to shared memory`` ()=
        let ast =
            aprim
                (Fetch(freshNode (Identifier "baz"), freshNode (Identifier "emp"), Direct))
        check
            ast
            [ normalBoolExpr (sbVar "baz") *<- normalBoolExpr (sbVar "emp") ]

    [<Test>]
    let ``model integer atomic assign from local to local memory`` () =
        let ast =
            aprim (Fetch(freshNode (Identifier "x"), freshNode (Identifier "x"), Direct))
        check
            ast
            [ normalIntExpr (siVar "x") *<- normalIntExpr (siVar "x") ]

    [<Test>]
    let ``model symbolic store <x = %{foo [|baz|]}>`` () =
        let ast =
            aprim
                (Fetch
                    (freshNode (Identifier "x"),
                     freshNode
                        (Symbolic
                            [ SymString "foo"
                              SymArg (freshNode (Identifier "baz")) ]),
                     Direct))
        check
            ast
            [ normalIntExpr (siVar "x")
              *<-
              normalIntExpr
                (IVar
                    (Sym
                        [ SymString "foo"
                          SymArg (normalBoolExpr (BVar (Reg "baz")))] )) ]


module CommandAxioms =
    open Starling.Core.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.GuardedView.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Lang.Modeller.Pretty

    let check (c : FullCommand) (cmd : ModellerPartCmd) : unit =
        assertOkAndEqual
            cmd
            (modelCommand sharedContext c)
            (printMethodError >> printUnstyled)

    let checkFail (c : FullCommand) (errors : MethodError list) : unit =
        assertFail
            errors
            (modelCommand sharedContext c)
            (printPartCmd (printViewExpr (printIteratedGView (printSym printVar))) >> printUnstyled)

    let prim (atom : DesugaredAtomic) : FullCommand =
        freshNode
        <| FPrim { PreLocals = []
                   Atomics = [ atom ]
                   PostLocals = [] }

    let lassign (lvalue : Expression) (rvalue : Expression) : FullCommand =
        freshNode
        <| FPrim { PreLocals = [ freshNode (Prim'.Fetch (lvalue, rvalue, Direct)) ]
                   Atomics = []
                   PostLocals = [] }

    [<Test>]
    let ``modelling local command with nonlocal lvalue fails`` () =
        let lv = freshNode (Identifier "y")
        let rv = freshNode (Identifier "bar")
        checkFail
            (lassign lv rv)
            [ BadLocal
                (freshNode (Prim'.Fetch (lv, rv, Direct)),
                 BadExprPair
                    (lv,
                     rv,
                     Var
                        ("y",
                         VarInWrongScope (expected = Thread, got = Shared)))) ]


    [<Test>]
    let ``modelling local command with nonlocal rvalue fails`` () =
        let lv = freshNode (Identifier "foo")
        let rv = freshNode (Identifier "x")
        checkFail
            (lassign lv rv)
            [ BadLocal
                (freshNode (Prim'.Fetch (lv, rv, Direct)),
                 BadExprPair
                    (lv,
                     rv,
                     Var
                        ("x",
                         VarInWrongScope (expected = Thread, got = Shared)))) ]

    [<Test>]
    let ``modelling command <foo = x> passes`` () =
        let ast = aprim (Fetch(freshNode (Identifier "foo"), freshNode (Identifier "x"), Direct))
        check
            (prim ast)
            (Prim [ normalIntExpr (siVar "foo") *<- normalIntExpr (siVar "x") ])

    [<Test>]
    let ``modelling command <foo = x++> passes`` () =
        let ast = aprim (Fetch(freshNode (Identifier "foo"), freshNode (Identifier "x"), Increment))
        check
            (prim ast)
            (Prim [ normalIntExpr (siVar "foo") *<- normalIntExpr (siVar "x")
                    normalIntExpr (siVar "x") *<- normalIntExpr (mkInc (siVar "x")) ])

    [<Test>]
    let ``modelling command <foo = x--> passes`` () =
        let ast = aprim (Fetch(freshNode (Identifier "foo"), freshNode (Identifier "x"), Decrement))
        check
            (prim ast)
            (Prim [ normalIntExpr (siVar "foo") *<- normalIntExpr (siVar "x")
                    normalIntExpr (siVar "x") *<- normalIntExpr (mkDec (siVar "x")) ])

    [<Test>]
    let ``modelling command <baz = y> passes`` () =
        let ast = aprim (Fetch(freshNode (Identifier "baz"), freshNode (Identifier "y"), Direct))
        check
            (prim ast)
            (Prim [ normalBoolExpr (sbVar "baz") *<- normalBoolExpr (sbVar "y") ])

    [<Test>]
    let ``model local Boolean symbolic load {baz = %{foo}(bar)}`` () =
        let ast =
            lassign
                (freshNode (Identifier "baz"))
                (freshNode
                    (Symbolic
                        [ SymString "foo"
                          SymArg (freshNode (Identifier "bar")) ] ))

        check
            ast
            (Prim
                [ (normalBoolExpr (sbVar "baz")
                   *<-
                   normalBoolExpr
                       (BVar
                           (Sym
                               [ SymString "foo"
                                 SymArg (normalIntExpr (IVar (Reg "bar"))) ]))) ] )


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
                  [ iterated (func "holdTick" [ Int (normalRec, "t0") ]) None ] ])

    [<Test>]
    let ``Search for size-2 viewdefs yields viewdefs up to size 2``() =
        check (Some 2) []
            (indefinites
                [ []
                  [ iterated (func "holdLock" []) None ]
                  [ iterated (func "holdLock" []) None
                    iterated (func "holdLock" []) None ]
                  [ iterated (func "holdLock" []) None
                    iterated (func "holdTick" [ Int (normalRec, "t0") ]) None ]
                  [ iterated (func "holdTick" [ Int (normalRec, "t0") ]) None ]
                  [ iterated (func "holdTick" [ Int (normalRec, "t0") ]) None
                    iterated (func "holdTick" [ Int (normalRec, "t1") ]) None ] ] )
