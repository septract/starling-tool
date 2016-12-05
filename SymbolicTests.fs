/// <summary>
///     Tests for <c>Symbolic</c>.
/// </summary>
module Starling.Tests.Core.Symbolic

open NUnit.Framework
open Starling.Collections
open Starling.Utils.Testing
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal

open Starling.Core.Pretty
open Starling.Core.Traversal.Pretty
open Starling.Core.Symbolic.Pretty


/// <summary>
///     Unit tests for symbolic post-state rewriting.
/// </summary>
module PostStateRewrite =
    let checkInt (expected : IntExpr<Sym<MarkedVar>>) (expr : IntExpr<Sym<Var>>)
      : unit =
        let trav = tliftToExprDest (traverseTypedSymWithMarker After)
        let res = mapTraversal (tliftToIntSrc trav) (normalInt expr)

        assertOkAndEqual expected res
            (printTraversalError (fun () -> String "?" ) >> printUnstyled)

    [<Test>]
    let ``Rewrite single variable to post-state`` () =
        checkInt (siAfter "target1") (siVar "target1")

    [<Test>]
    let ``Rewrite expression with one variable to post-state`` () =
        checkInt
            (IAdd [IInt 4L; siAfter "target1"])
            (IAdd [IInt 4L; siVar "target1"])

    [<Test>]
    let ``Rewrite expression with two variables to post-state`` () =
        checkInt
            (ISub [siAfter "target1"; siAfter "target2"])
            (ISub [siVar "target1"; siVar "target2"])

    [<Test>]
    let ``Rewrite expression with no variables to post-state`` () =
        checkInt (IDiv (IInt 6L, IInt 0L)) (IDiv (IInt 6L, IInt 0L))


/// <summary>
///     Test cases for testing underapproximation of Booleans.
/// </summary>
module BoolApprox =
    let check
      (expected : BoolExpr<Sym<MarkedVar>>)
      (ctx : TraversalContext<unit>)
      (expr : BoolExpr<Sym<MarkedVar>>)
      : unit =
        let result = tliftToBoolSrc approx ctx (normalBool expr)
        assertOkAndEqual (ctx, expected) result
            (printTraversalError (fun () -> String "?" ) >> printUnstyled)

    [<Test>]
    let ``Don't alter +ve symbol-less expression`` () =
        check
            (BAnd
                [ bEq (sbBefore "foo") (sbAfter "bar")
                  BGt (normalInt (siBefore "baz"), normalInt (IInt 1L)) ] )
            (Context.positive ())
            (BAnd
                [ bEq (sbBefore "foo") (sbAfter "bar")
                  BGt (normalInt (siBefore "baz"), normalInt (IInt 1L)) ] )

    [<Test>]
    let ``Rewrite +ve param-less Bool symbol to false`` () =
        check
            BFalse
            (Context.positive ())
            (BVar (Sym { Sentence = [ SymString "test" ]; Args = ([] : SMExpr list) } ))

    [<Test>]
    let ``Rewrite -ve param-less Bool symbol to true`` () =
        check
            BTrue
            (Context.negative ())
            (BVar (Sym { Sentence = [ SymString "test" ]; Args = ([] : SMExpr list) } ))

    [<Test>]
    let ``Rewrite +ve Reg-params Bool symbol to false`` () =
        check
            BFalse
            (Context.positive ())
            (BVar
                (Sym
                    { Sentence = [ SymString "test" ]
                      Args =
                        [ normalIntExpr (siBefore "foo")
                          normalBoolExpr (sbAfter "bar") ] } ))

    [<Test>]
    let ``Rewrite -ve Reg-params Bool symbol to true`` () =
        check
            BTrue
            (Context.negative ())
            (BVar
                (Sym
                    { Sentence = [ SymString "test" ]
                      Args =
                        [ normalIntExpr (siBefore "foo")
                          normalBoolExpr (sbAfter "bar") ] } ))

    [<Test>]
    let ``Rewrite +ve implication correctly`` () =
        check
            (BImplies (BTrue, BFalse))
            (Context.positive ())
            (BImplies
                (BVar
                    (Sym
                        { Sentence = [ SymString "test1" ]
                          Args =
                            [ normalIntExpr (siBefore "foo")
                              normalBoolExpr (sbAfter "bar") ] } ),
                 BVar
                    (Sym
                        { Sentence = [ SymString "test2" ]
                          Args =
                              [ normalIntExpr (siBefore "baz")
                                normalBoolExpr (sbAfter "barbaz") ] } )))

    [<Test>]
    let ``Rewrite -ve implication correctly`` () =
        check
            (BImplies (BFalse, BTrue))
            (Context.negative ())
            (BImplies
                (BVar
                    (Sym
                        { Sentence = [ SymString "test1" ]
                          Args =
                            [ normalIntExpr (siBefore "foo")
                              normalBoolExpr (sbAfter "bar") ] } ),
                 BVar
                    (Sym
                        { Sentence = [ SymString "test2" ]
                          Args =
                            [ normalIntExpr (siBefore "baz")
                              normalBoolExpr (sbAfter "barbaz") ] } )))


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
        let result = findVars (tliftOverExpr collectSymVars) expr

        assertOkAndEqual (Set.ofList expected) result
            (printTraversalError (fun () -> String "?" ) >> printUnstyled)

    [<Test>]
    let ``Finding vars in a Boolean primitive returns empty`` () =
        check [] (normalBoolExpr BTrue)

    [<Test>]
    let ``Finding vars in an integer primitive returns empty`` () =
        check [] (normalIntExpr (IInt 1L))

    [<Test>]
    let ``Finding vars in a Boolean var returns that var`` () =
        check [ normalBoolVar (Before "foo") ] (normalBoolExpr (sbBefore "foo"))

    [<Test>]
    let ``Finding vars in an integer var returns that var`` () =
        check [ normalIntVar (After "bar") ] (normalIntExpr (siAfter "bar"))

    [<Test>]
    let ``Finding vars in a Boolean expression works correctly`` () =
        check
            [ normalBoolVar (Before "foo")
              normalBoolVar (After "baz")
              normalIntVar (Before "foobar")
              normalIntVar (After "barbaz") ]
            (normalBoolExpr
                (BAnd
                    [ BOr [ sbBefore "foo"; sbAfter "baz" ]
                      BGt ( normalInt (siBefore "foobar"), normalInt (siAfter "barbaz")) ] ))

    [<Test>]
    let ``Finding vars in an integer expression works correctly`` () =
        check
            [ normalIntVar (Before "foo")
              normalIntVar (After "bar")
              normalIntVar (Before "foobar")
              normalIntVar (After "barbaz") ]
            (normalIntExpr
                (IAdd
                    [ ISub [ siBefore "foo"; siAfter "bar" ]
                      IMul [ siBefore "foobar"; siAfter "barbaz" ]] ))

    [<Test>]
    let ``Finding vars in an Boolean symbol works correctly`` () =
        check
            [ normalIntVar (Before "bar")
              normalBoolVar (After "baz") ]
            (normalBoolExpr
                (BVar
                    (sym [ SymString "foo" ]
                        [ normalIntExpr (siBefore "bar")
                          normalBoolExpr (sbAfter "baz") ] )))

    [<Test>]
    let ``Finding vars in an integer symbol works correctly`` () =
        check
            [ normalIntVar (Before "bar"); normalBoolVar (After "baz") ]
            (normalIntExpr
                (IVar
                    (sym [ SymString "foo" ]
                        [ normalIntExpr (siBefore "bar")
                          normalBoolExpr (sbAfter "baz") ] )))


/// <summary>
///     Tests on the symbolic pretty printer.
/// </summary>
module Pretty =
    open Starling.Core.Symbolic.Pretty

    [<Test>]
    let ``Pretty-printing a symbolic sentence without interpolation works`` () =
        let sentence =
            [ SymString "foo("
              SymParamRef 2
              SymString ", "
              SymParamRef 1
              SymString ")" ]
        "foo(#2, #1)"
            ?=? printUnstyled (printSymbolicSentence sentence)

    [<Test>]
    let ``Pretty-printing a valid Sym interpolates variables properly`` () =
        let sentence =
            [ SymString "foo("
              SymParamRef 2
              SymString ", "
              SymParamRef 1
              SymString ")" ]
        let args = [ normalIntExpr (siVar "bar"); normalBoolExpr (sbVar "baz") ]

        "(sym 'foo(baz, bar)')"
            ?=? printUnstyled (printSym String (sym sentence args))

    [<Test>]
    let ``Pretty-printing an invalid Sym interpolates errors properly`` () =
        let sentence =
            [ SymString "nope("
              SymParamRef 2
              SymString ", "
              SymParamRef 0 // error
              SymString ", "
              SymParamRef 3 // error
              SymString ")" ]
        let args = [ normalIntExpr (siVar "bar"); normalBoolExpr (sbVar "baz") ]

        "(sym 'nope(baz, #ERROR#, #ERROR#)')"
            ?=? printUnstyled (printSym String (sym sentence args))
