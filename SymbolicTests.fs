/// <summary>
///     Tests for <c>Symbolic</c>.
/// </summary>
module Starling.Tests.Core.Symbolic

open NUnit.Framework
open Starling.Utils.Testing
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Sub
open Starling.Core.Symbolic

open Starling.Core.Pretty
open Starling.Core.Sub.Pretty
open Starling.Core.Symbolic.Pretty


/// <summary>
///     Unit tests for symbolic post-state rewriting.
/// </summary>
module PostStateRewrite =
    let checkInt (expected : IntExpr<Sym<MarkedVar>>) (expr : IntExpr<Sym<Var>>)
      : unit =
        let trav = tliftToExprDest (traverseTypedSymWithMarker After)
        let res = mapTraversal (intSubVars trav) expr

        assertOkAndEqual expected res
            (printSubError (fun () -> String "?" ) >> printUnstyled)

    [<Test>]
    let ``Rewrite single variable to post-state`` () =
        checkInt (siAfter "target1") (siVar "target1")

    [<Test>]
    let ``Rewrite expression with one variable to post-state`` () =
        checkInt
            (AAdd [AInt 4L; siAfter "target1"])
            (AAdd [AInt 4L; siVar "target1"])

    [<Test>]
    let ``Rewrite expression with two variables to post-state`` () =
        checkInt
            (ASub [siAfter "target1"; siAfter "target2"])
            (ASub [siVar "target1"; siVar "target2"])

    [<Test>]
    let ``Rewrite expression with no variables to post-state`` () =
        checkInt (ADiv (AInt 6L, AInt 0L)) (ADiv (AInt 6L, AInt 0L))


/// <summary>
///     Test cases for testing underapproximation of Booleans.
/// </summary>
module BoolApprox =
    let check
      (expected : BoolExpr<Sym<MarkedVar>>)
      (ctx : TraversalContext)
      (expr : BoolExpr<Sym<MarkedVar>>)
      : unit =
        let result = boolSubVars approx ctx expr
        assertOkAndEqual (ctx, expected) result
            (printSubError (fun () -> String "?" ) >> printUnstyled)

    [<Test>]
    let ``Don't alter +ve symbol-less expression`` () =
        check
            (BAnd
                [ bEq (sbBefore "foo") (sbAfter "bar")
                  BGt (siBefore "baz", AInt 1L) ] )
            Context.positive
            (BAnd
                [ bEq (sbBefore "foo") (sbAfter "bar")
                  BGt (siBefore "baz", AInt 1L) ] )

    [<Test>]
    let ``Rewrite +ve param-less Bool symbol to false`` () =
        check
            BFalse
            Context.positive
            (BVar (Sym { Name = "test"; Params = ([] : SMExpr list) } ))

    [<Test>]
    let ``Rewrite -ve param-less Bool symbol to true`` () =
        check
            BTrue
            Context.negative
            (BVar (Sym { Name = "test"; Params = ([] : SMExpr list) } ))

    [<Test>]
    let ``Rewrite +ve Reg-params Bool symbol to false`` () =
        check
            BFalse
            Context.positive
            (BVar
                (Sym
                    { Name = "test"
                      Params =
                        [ Expr.Int (siBefore "foo")
                          Expr.Bool (sbAfter "bar") ] } ))

    [<Test>]
    let ``Rewrite -ve Reg-params Bool symbol to true`` () =
        check
            BTrue
            Context.negative
            (BVar
                (Sym
                    { Name = "test"
                      Params =
                        [ Expr.Int (siBefore "foo")
                          Expr.Bool (sbAfter "bar") ] } ))

    [<Test>]
    let ``Rewrite +ve implication correctly`` () =
        check
            (BImplies (BTrue, BFalse))
            Context.positive
            (BImplies
                (BVar
                    (Sym
                        { Name = "test1"
                          Params =
                            [ Expr.Int (siBefore "foo")
                              Expr.Bool (sbAfter "bar") ] } ),
                 BVar
                    (Sym
                        { Name = "test2"
                          Params =
                              [ Expr.Int (siBefore "baz")
                                Expr.Bool (sbAfter "barbaz") ] } )))

    [<Test>]
    let ``Rewrite -ve implication correctly`` () =
        check
            (BImplies (BFalse, BTrue))
            Context.negative
            (BImplies
                (BVar
                    (Sym
                        { Name = "test1"
                          Params =
                            [ Expr.Int (siBefore "foo")
                              Expr.Bool (sbAfter "bar") ] } ),
                 BVar
                    (Sym
                        { Name = "test2"
                          Params =
                            [ Expr.Int (siBefore "baz")
                              Expr.Bool (sbAfter "barbaz") ] } )))


/// <summary>
///     Test cases for finding variables in expressions.
/// </summary>
module FindSMVarsCases =
    /// <summary>
    ///     Tests finding variables in symbolic expressions.
    /// </summary>
    let check
      (expected : CTyped<MarkedVar> list)
      (expr : Expr<Sym<MarkedVar>>)
      : unit =
        let result =
            findMarkedVars (tliftOverExpr collectSymMarkedVars) expr

        assertOkAndEqual (Set.ofList expected) result
            (printSubError (fun () -> String "?" ) >> printUnstyled)

    [<Test>]
    let ``Finding vars in a Boolean primitive returns empty`` () =
        check [] (Expr.Bool BTrue)

    [<Test>]
    let ``Finding vars in an integer primitive returns empty`` () =
        check [] (Expr.Int (AInt 1L))

    [<Test>]
    let ``Finding vars in a Boolean var returns that var`` () =
        check [ CTyped.Bool (Before "foo") ] (Expr.Bool (sbBefore "foo"))

    [<Test>]
    let ``Finding vars in an integer var returns that var`` () =
        check [ CTyped.Int (After "bar") ] (Expr.Int (siAfter "bar"))

    [<Test>]
    let ``Finding vars in a Boolean expression works correctly`` () =
        check
            [ CTyped.Bool (Before "foo")
              CTyped.Bool (After "baz")
              CTyped.Int (Before "foobar")
              CTyped.Int (After "barbaz") ]
            (Expr.Bool
                (BAnd
                    [ BOr [ sbBefore "foo"; sbAfter "baz" ]
                      BGt ( siBefore "foobar", siAfter "barbaz" ) ] ))

    [<Test>]
    let ``Finding vars in an integer expression works correctly`` () =
        check
            [ CTyped.Int (Before "foo")
              CTyped.Int (After "bar")
              CTyped.Int (Before "foobar")
              CTyped.Int (After "barbaz") ]
            (Expr.Int
                (AAdd
                    [ ASub [ siBefore "foo"; siAfter "bar" ]
                      AMul [ siBefore "foobar"; siAfter "barbaz" ]] ))

    [<Test>]
    let ``Finding vars in an Boolean symbol works correctly`` () =
        check
            [ CTyped.Int (Before "bar")
              CTyped.Bool (After "baz") ]
            (Expr.Bool
                (BVar
                    (sym "foo"
                        [ Expr.Int (siBefore "bar")
                          Expr.Bool (sbAfter "baz") ] )))

    [<Test>]
    let ``Finding vars in an integer symbol works correctly`` () =
        check
            [ CTyped.Int (Before "bar"); CTyped.Bool (After "baz") ]
            (Expr.Int
                (AVar
                    (sym "foo"
                        [ Expr.Int (siBefore "bar")
                          Expr.Bool (sbAfter "baz") ] )))
