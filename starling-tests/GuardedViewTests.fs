/// <summary>
///     Tests for guarded views.
/// </summary>
///
module Starling.Tests.GuardedView

open Chessie.ErrorHandling
open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.Collections

open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Traversal
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.TypeSystem

/// <summary>
///     Test traversal for position-based substitution.
/// </summary>
let positionTestSub : Traversal<Expr<Var>, Expr<Var>, unit, unit> =
    let ptsVar ctx tv =
        let exp =
            match typeOf tv with
            | AnIntR ty ->
                let v =
                    match ctx with
                    | Positions (Positive::xs) -> IInt 1L
                    | Positions (Negative::xs) -> IInt 0L
                    | _ -> IInt -1L
                Expr.Int (ty, v)
            | AnArrayR ty ->
                let v =
                    match ctx with
                    | Positions (Positive::xs) -> AVar "pos"
                    | Positions (Negative::xs) -> AVar "neg"
                    | _ -> AVar "?"
                Expr.Array (ty, v)
            | ABoolR ty ->
                let v =
                    match ctx with
                    | Positions (x::xs) -> Context.overapprox x
                    | _ -> BVar "?"
                Expr.Bool (ty, v)
        ok (ctx, exp)
    tliftToExprSrc ptsVar

/// <summary>
///     Case studies for testing Term traversal.
/// </summary>
module TermTraversal =
    open Starling.Tests.TestUtils
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty

    /// <summary>
    ///     Tests term traversal on positional substitutions.
    /// </summary>
    let check
      (expected : Term<BoolExpr<Var>, GView<Var>, Func<Expr<Var>>>)
      (pos : TraversalContext<unit>)
      (gv : Term<BoolExpr<Var>, GView<Var>, Func<Expr<Var>>>) : unit =
        let trav = tliftOverTerm positionTestSub
        let result = trav pos gv

        assertOkAndEqual (pos, expected) result
            (printTraversalError (fun _ -> String "?") >> printUnstyled)

    [<Test>]
    let ``successfully translate a positive Term`` () =
        check
            { Cmd = BAnd [ bEq BFalse BFalse; bEq BFalse (BNot BTrue) ]
              WPre =
                Multiset.ofFlatList
                    [ gfunc BTrue "bar"
                        [ normalIntExpr (IInt 0L); normalBoolExpr BFalse ]
                      gfunc (BGt (normalInt (IInt 1L), normalInt (IInt 1L))) "barbaz"
                        [ normalIntExpr (IAdd [ IInt 0L; IInt 0L ]) ] ]
              Goal =
                (regFunc "bar" [ normalIntExpr (IInt 1L); normalBoolExpr BTrue ]) }
            (Context.positive ())
            { Cmd =
                BAnd
                    [ bEq (BVar "foo") (BVar "bar")
                      bEq (BVar "baz") (BNot (BVar "baz")) ]
              WPre =
                Multiset.ofFlatList
                    [ gfunc (BVar "foo") "bar"
                        [ normalIntExpr (IVar "baz")
                          normalBoolExpr (BVar "fizz") ]
                      gfunc (BGt (normalInt (IVar "foobar"), normalInt (IVar "barbar"))) "barbaz"
                        [ normalIntExpr
                            (IAdd [ IVar "foobaz"; IVar "bazbaz" ]) ] ]
              Goal =
                regFunc "bar"
                    [ normalIntExpr (IVar "baz")
                      normalBoolExpr (BVar "barbaz") ] }

    [<Test>]
    let ``Successfully translate a negative DTerm`` () =
        check
            { Cmd = BAnd [ bEq BTrue BTrue; bEq BTrue (BNot BFalse) ]
              WPre =
                Multiset.ofFlatList
                    [ gfunc BFalse "bar"
                        [ normalIntExpr (IInt 1L); normalBoolExpr BTrue ]
                      gfunc (BGt (normalInt (IInt 0L), normalInt (IInt 0L))) "barbaz"
                        [ normalIntExpr (IAdd [ IInt 1L; IInt 1L ]) ] ]
              Goal =
                regFunc "bar" [ normalIntExpr (IInt 0L); normalBoolExpr BFalse ] }
            (Context.negative ())
            { Cmd =
                BAnd
                    [ bEq (BVar "foo") (BVar "bar")
                      bEq (BVar "baz") (BNot (BVar "baz")) ]
              WPre =
                Multiset.ofFlatList
                    [ gfunc (BVar "foo") "bar"
                        [ normalIntExpr (IVar "baz"); normalBoolExpr (BVar "fizz") ]
                      gfunc (BGt (normalInt (IVar "foobar"), normalInt (IVar "barbar"))) "barbaz"
                        [ normalIntExpr
                            (IAdd [ IVar "foobaz"; IVar "bazbaz" ]) ] ]
              Goal =
                regFunc "bar"
                   [ normalIntExpr (IVar "baz"); normalBoolExpr (BVar "barbaz") ] }

/// <summary>
///     Case studies for testing GFunc traversal.
/// </summary>
module GFuncTraversal =
    open Starling.Tests.TestUtils
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty

    /// <summary>
    ///     Tests GFunc traversal on positional substitutions.
    /// </summary>
    let check
      (expected : GFunc<Var>)
      (pos : TraversalContext<unit>)
      (gv : GFunc<Var>) : unit =
        let trav = tliftOverGFunc positionTestSub
        let result = trav pos gv

        assertOkAndEqual (pos, expected) result
            (printTraversalError (fun _ -> String "?") >> printUnstyled)

    [<Test>]
    let ``GFunc substitution in +ve case works properly`` () =
        check
            (gfunc BFalse "bar" [ normalIntExpr (IInt 1L); normalBoolExpr BTrue ] )
            (Context.positive ())
            (gfunc (BVar "foo") "bar"
                [ normalIntExpr (IVar "baz"); normalBoolExpr (BVar "fizz") ] )

    [<Test>]
    let ``GFunc substitution in -ve case works properly`` () =
        check
            (gfunc BTrue "bar" [ normalIntExpr (IInt 0L); normalBoolExpr BFalse ] )
            (Context.negative ())
            (gfunc (BVar "foo") "bar"
                [ normalIntExpr (IVar "baz"); normalBoolExpr (BVar "fizz") ])

/// <summary>
///     Case studies for testing GView traversal.
/// </summary>
module GViewTraversal =
    open Starling.Tests.TestUtils
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty

    /// <summary>
    ///     Tests GView traversal on positional substitutions.
    /// </summary>
    let check
      (expected : GView<Var>)
      (pos : TraversalContext<unit>)
      (gv : GView<Var>) : unit =
        let trav = tchainM (tliftOverGFunc positionTestSub) id
        let result = trav pos gv

        assertOkAndEqual (pos, expected) result
            (printTraversalError (fun _ -> String "?") >> printUnstyled)

    [<Test>]
    let ``+ve empty GView substitution is a no-op`` () =
        check Multiset.empty (Context.positive ()) Multiset.empty

    [<Test>]
    let ``-ve empty GView substitution is a no-op`` () =
        check Multiset.empty (Context.negative ()) Multiset.empty

    [<Test>]
    let ``Singleton GView substitution in +ve case works properly`` () =
        check
            (Multiset.singleton
                (gfunc BFalse "bar"
                    [ normalIntExpr (IInt 1L)
                      normalBoolExpr BTrue ] ))
            (Context.positive ())
            (Multiset.singleton
                (gfunc (BVar "foo") "bar"
                    [ normalIntExpr (IVar "baz")
                      normalBoolExpr (BVar "fizz") ] ))

    [<Test>]
    let ``Singleton GView substitution in -ve case works properly`` () =
        check
            (Multiset.singleton
                (gfunc BTrue "bar"
                    [ normalIntExpr (IInt 0L); normalBoolExpr BFalse ] ))
            (Context.negative ())
            (Multiset.singleton
                (gfunc (BVar "foo") "bar"
                    [ normalIntExpr (IVar "baz")
                      normalBoolExpr (BVar "fizz") ] ))

    [<Test>]
    let ``Multi GView substitution in +ve case works properly`` () =
        check
            (Multiset.ofFlatList
                [ gfunc BFalse "bar"
                    [ normalIntExpr (IInt 1L)
                      normalBoolExpr BTrue ]
                  gfunc (BGt (normalInt (IInt 0L), normalInt (IInt 0L))) "barbaz"
                    [ normalIntExpr
                          (IAdd [ IInt 1L; IInt 1L ]) ] ] )
            (Context.positive ())
            (Multiset.ofFlatList
                [ gfunc (BVar "foo") "bar"
                    [ normalIntExpr (IVar "baz")
                      normalBoolExpr (BVar "fizz") ]
                  gfunc (BGt (normalInt (IVar "foobar"), normalInt (IVar "barbar"))) "barbaz"
                    [ normalIntExpr
                          (IAdd [ IVar "foobaz"; IVar "bazbaz" ]) ] ] )

    [<Test>]
    let ``Multi GView substitution in -ve case works properly`` () =
        check
            (Multiset.ofFlatList
                [ gfunc BTrue "bar"
                    [ normalIntExpr (IInt 0L); normalBoolExpr BFalse ]
                  gfunc (BGt (normalInt (IInt 1L), normalInt (IInt 1L))) "barbaz"
                    [ normalIntExpr (IAdd [ IInt 0L; IInt 0L ]) ] ] )
            (Context.negative ())
            (Multiset.ofFlatList
                [ gfunc (BVar "foo") "bar"
                    [ normalIntExpr (IVar "baz"); normalBoolExpr (BVar "fizz") ]
                  gfunc (BGt (normalInt (IVar "foobar"), normalInt (IVar "barbar"))) "barbaz"
                    [ normalIntExpr
                          (IAdd [ IVar "foobaz"; IVar "bazbaz" ]) ] ] )
