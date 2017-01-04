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
    let ``test unknown func`` () =
        check
            (View.Func <| afunc "badfunc" [])
            ([ NoSuchView "badfunc" ])

    [<Test>]
    let ``test missing parameter`` () =
        check
            (View.Func <| afunc "holdTick" [])
            ([ LookupError ("holdTick", CountMismatch(0, 1)) ])

    [<Test>]
    let ``test bad parameter type`` () =
        check
          (View.Func <| afunc "holdTick" [freshNode Expression'.True])
          ([ LookupError
               ( "holdTick",
                 Error.TypeMismatch
                   (Int (normalRec, "t"), Type.Bool (indefRec, ()))) ])

    [<Test>]
    let ``test bad parameter subtype`` () =
        check
          (View.Func <| afunc "holdTick" [freshNode (Identifier "lnode")])
          ([ LookupError
               ( "holdTick",
                 Error.TypeMismatch
                   (normalIntVar "t", Type.Int ({ PrimSubtype = Named "Node" }, ()))) ])


module ArithmeticExprs =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Lang.Modeller.Pretty

    let check (env : VarMap) (ast : Expression) (expectedExpr : TypedIntExpr<Sym<Var>>) =
        assertOkAndEqual
            expectedExpr
            (modelIntExpr env environ id ast)
            (printExprError >> printUnstyled)

    let checkFail (env : VarMap) (ast : Expression) (expectedErrors : ExprError list) =
        assertFail
            expectedErrors
            (modelIntExpr env environ id ast)
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
                     IAdd [ IVar (Reg "foo"); IInt 3L ])))

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
        let actualBoolExpr = okOption <| modelBoolExpr env environ id ast
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

module Atomics =
    open Starling.Core.Pretty
    open Starling.Lang.Modeller.Pretty

    let check (ast : Atomic) (cmd : PrimCommand) : unit =
        assertOkAndEqual
            cmd
            (modelAtomic sharedContext ast)
            (printPrimError >> printUnstyled)

    [<Test>]
    let ``model integer load primitive <foo = x++>`` ()=
        let ast = freshNode (Fetch(freshNode (Identifier "foo"), freshNode (Identifier "x"), Increment))
        check
            ast
            <| command' "!ILoad++"
                ast
                [ normalIntExpr (siVar "foo"); normalIntExpr (siVar "x") ]
                [ normalIntExpr (siVar "x") ]

    [<Test>]
    let ``model Boolean load primitive <baz = y>`` ()=
        let ast = freshNode (Fetch(freshNode (Identifier "baz"), freshNode (Identifier "y"), Direct))
        check
            ast
            (command' "!BLoad" ast [ normalBoolExpr (sbVar "baz") ] [ normalBoolExpr (sbVar "y") ])

    [<Test>]
    let ``model symbolic store <x = %{foo}(baz)>`` () =
        let ast =
            freshNode
                (Fetch
                    (freshNode (Identifier "x"),
                     freshNode
                        (Symbolic
                          { Sentence = [ SymString "foo" ]
                            Args = [ freshNode (Identifier "baz") ] }),
                     Direct))
        check
            ast
            (Intrinsic
                (IAssign
                    { AssignType = Store
                      TypeRec = normalRec
                      LValue = IVar (Reg "x")
                      RValue =
                        IVar
                            (sym
                                [ SymString "foo" ]
                                [ normalBoolExpr (BVar (Reg "baz")) ] ) } ))


module CommandAxioms =
    open Starling.Core.Pretty
    open Starling.Lang.Modeller.Pretty

    let check (c : Command<ViewExpr<View>>) (cmd : ModellerPartCmd) : unit =
        assertOkAndEqual
            cmd
            (modelCommand sharedContext c)
            (printMethodError >> printUnstyled)

    let prim (atom : Atomic) : Command<ViewExpr<View>> =
        freshNode
        <| Command'.Prim { PreAssigns = []
                           Atomics = [ atom ]
                           PostAssigns = [] }

    let local (lvalue : Expression) (rvalue : Expression)
      : Command<ViewExpr<View>> =
        freshNode
        <| Command'.Prim { PreAssigns = [ (lvalue, rvalue) ]
                           Atomics = []
                           PostAssigns = [] }

    [<Test>]
    let ``modelling command <foo = x++> passes`` () =
        let ast = freshNode (Fetch(freshNode (Identifier "foo"), freshNode (Identifier "x"), Increment))
        check
            (prim <| ast)
            <| Prim ([ command' "!ILoad++"
                        ast
                        [ normalIntExpr (siVar "foo"); normalIntExpr (siVar "x") ]
                        [ normalIntExpr (siVar "x") ] ])

    [<Test>]
    let ``modelling command <baz = y> passes`` () =
        let ast = freshNode (Fetch(freshNode (Identifier "baz"), freshNode (Identifier "y"), Direct))
        check
            (prim <| ast)
            <| Prim ([ command' "!BLoad"
                        ast
                        [ normalBoolExpr (sbVar "baz") ]
                        [ normalBoolExpr (sbVar "y") ] ])

    [<Test>]
    let ``model local Boolean symbolic load {baz = %{foo}(bar)}`` () =
        let ast =
            local
                (freshNode (Identifier "baz"))
                (freshNode
                    (Symbolic
                        { Sentence = [ SymString "foo" ]
                          Args = [ freshNode (Identifier "bar") ] }))

        check
            ast
            (Prim
                [ Intrinsic
                    ( BAssign
                        { AssignType = Local
                          TypeRec = normalRec
                          LValue = BVar (Reg "baz")
                          RValue =
                            BVar
                                (sym
                                    [ SymString "foo" ]
                                    [ normalIntExpr (IVar (Reg "bar")) ])})])


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
