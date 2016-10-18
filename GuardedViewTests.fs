/// <summary>
///     Tests for guarded views.
/// </summary>
///
module Starling.Tests.GuardedView

open Chessie.ErrorHandling

open Starling.Utils
open Starling.Collections

open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Sub
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.Symbolic
open Starling.Core.Model

module Tests =
    open NUnit.Framework

    open Starling.Utils.Testing
    open Starling.Core.TypeSystem

    /// <summary>
    ///     Test traversal for position-based substitution.
    /// </summary>
    let positionTestSub : Traversal<Expr<Var>, Expr<Var>, unit> =
        let ptsVar ctx tv =
            let exp =
                match (typeOf tv) with
                | Int () ->
                    match ctx with
                    | Positions (Positive::xs) -> AInt 1L
                    | Positions (Negative::xs) -> AInt 0L
                    | _ -> AInt -1L
                    |> Int
                | Bool () ->
                    match ctx with
                    | Positions (x::xs) -> Context.overapprox x
                    | _ -> BVar "?"
                    |> Bool
            ok (ctx, exp)
        liftTraversalToExprSrc ptsVar

    /// <summary>
    ///     NUnit tests for guarded views.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Case studies for <c>testPositionSubExprInGFunc</c>.
        /// </summary>
        static member PositionSubExprInGFuncCases =
            [ (tcd
                   [| gfunc (BVar "foo") "bar"
                          [ Typed.Int (AVar "baz")
                            Typed.Bool (BVar "fizz") ]
                      Context.positive |] )
                  .Returns(
                      ok <|
                      (Context.positive,
                       (gfunc BFalse "bar"
                            [ Typed.Int (AInt 1L)
                              Typed.Bool BTrue ] : GFunc<Var> )))
                  .SetName("GFunc substitution in +ve case works properly")
              (tcd
                   [| gfunc (BVar "foo") "bar"
                          [ Typed.Int (AVar "baz")
                            Typed.Bool (BVar "fizz") ]
                      Context.negative |] )
                  .Returns(
                      ok <|
                      (Context.negative,
                       (gfunc BTrue "bar"
                            [ Typed.Int (AInt 0L)
                              Typed.Bool BFalse ] : GFunc<Var> )))
                  .SetName("GFunc substitution in -ve case works properly") ]

        /// <summary>
        ///     Tests <c>subExprInGFunc</c> on positional substitutions.
        /// </summary>
        [<TestCaseSource("PositionSubExprInGFuncCases")>]
        member this.testPositionSubExprInGFunc
          (gf : GFunc<Var>)
          (pos : TraversalContext) =
            let trav = liftTraversalOverGFunc positionTestSub
            let result = trav pos gf
            okOption result

        /// <summary>
        ///     Case studies for <c>testPositionSubExprInGView</c>.
        /// </summary>
        static member PositionSubExprInGViewCases =
            [ (tcd
                   [| (Multiset.empty : GView<Var>)
                      Context.positive |] )
                  .Returns(
                      ok <|
                      (Context.positive,
                       (Multiset.empty : GView<Var>)))
                  .SetName("+ve empty GView substitution is a no-op")
              (tcd
                   [| (Multiset.empty : GView<Var>)
                      Context.negative |] )
                  .Returns(
                      ok <|
                      (Context.negative,
                       (Multiset.empty : GView<Var>)))
                  .SetName("-ve empty GView substitution is a no-op")
              (tcd
                   [| Multiset.singleton
                          (gfunc (BVar "foo") "bar"
                               [ Typed.Int (AVar "baz")
                                 Typed.Bool (BVar "fizz") ] )
                      Context.positive |] )
                  .Returns(
                      ok <|
                      (Context.positive,
                       (Multiset.singleton
                            (gfunc BFalse "bar"
                                 [ Typed.Int (AInt 1L)
                                   Typed.Bool BTrue ] ) : GView<Var> )))
                  .SetName("Singleton GView substitution in +ve case works properly")
              (tcd
                   [| Multiset.singleton
                          (gfunc (BVar "foo") "bar"
                               [ Typed.Int (AVar "baz")
                                 Typed.Bool (BVar "fizz") ] )
                      Context.negative |] )
                  .Returns(
                      ok <|
                      (Context.negative,
                       (Multiset.singleton
                            (gfunc BTrue "bar"
                                 [ Typed.Int (AInt 0L)
                                   Typed.Bool BFalse ] ) : GView<Var> )))
                  .SetName("Singleton GView substitution in -ve case works properly")
              (tcd
                   [| Multiset.ofFlatList
                          [ gfunc (BVar "foo") "bar"
                                [ Typed.Int (AVar "baz")
                                  Typed.Bool (BVar "fizz") ]
                            gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                [ Typed.Int
                                      (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                      Context.positive |] )
                  .Returns(
                      ok <|
                      (Context.positive,
                       (Multiset.ofFlatList
                            [ gfunc BFalse "bar"
                                  [ Typed.Int (AInt 1L)
                                    Typed.Bool BTrue ]
                              gfunc (BGt (AInt 0L, AInt 0L)) "barbaz"
                                  [ Typed.Int
                                        (AAdd [ AInt 1L; AInt 1L ]) ] ]
                        : GView<Var>)))
                  .SetName("Multi GView substitution in +ve case works properly")
              (tcd
                   [| Multiset.ofFlatList
                          [ gfunc (BVar "foo") "bar"
                                [ Typed.Int (AVar "baz")
                                  Typed.Bool (BVar "fizz") ]
                            gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                [ Typed.Int
                                      (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                      Context.negative |] )
                  .Returns(
                      ok <|
                      (Context.negative,
                       (Multiset.ofFlatList
                            [ gfunc BTrue "bar"
                                  [ Typed.Int (AInt 0L)
                                    Typed.Bool BFalse ]
                              gfunc (BGt (AInt 1L, AInt 1L)) "barbaz"
                                  [ Typed.Int
                                        (AAdd [ AInt 0L; AInt 0L ]) ] ]
                        : GView<Var>)))
                  .SetName("Multi GView substitution in -ve case works properly") ]

        /// <summary>
        ///     Tests <c>subExprInGView</c> on positional substitutions.
        /// </summary>
        [<TestCaseSource("PositionSubExprInGViewCases")>]
        member this.testPositionSubExprInGView
          (gv : GView<Var>)
          (pos : TraversalContext) =
            let trav = tchainM (liftTraversalOverGFunc positionTestSub) id
            let result = trav pos gv
            okOption result

        /// <summary>
        ///     Case studies for <c>testPositionSubExprInDTerm</c>.
        /// </summary>
        static member PositionSubExprInDTermCases =
            [ (tcd
                   [| ( { Cmd =
                              BAnd
                                  [ bEq (BVar "foo") (BVar "bar")
                                    bEq (BVar "baz") (BNot (BVar "baz")) ]
                          WPre =
                              Multiset.ofFlatList
                                  [ gfunc (BVar "foo") "bar"
                                        [ Typed.Int (AVar "baz")
                                          Typed.Bool (BVar "fizz") ]
                                    gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                        [ Typed.Int
                                              (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                          Goal =
                              (vfunc "bar"
                                   [ Typed.Int (AVar "baz")
                                     Typed.Bool (BVar "barbaz") ] : VFunc<Var> ) }
                       : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )
                      Context.positive |] )
                  .Returns(
                      ok <|
                      (Context.positive,
                       ( { Cmd =
                               BAnd
                                   [ bEq BFalse BFalse
                                     bEq BFalse (BNot BTrue) ]
                           WPre =
                               Multiset.ofFlatList
                                   [ gfunc BTrue "bar"
                                         [ Typed.Int (AInt 0L)
                                           Typed.Bool BFalse ]
                                     gfunc (BGt (AInt 1L, AInt 1L)) "barbaz"
                                         [ Typed.Int
                                               (AAdd [ AInt 0L; AInt 0L ]) ] ]
                           Goal =
                               (vfunc "bar"
                                    [ Typed.Int (AInt 1L)
                                      Typed.Bool BTrue ] : VFunc<Var> ) }
                        : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )))
                  .SetName("Successfully translate a positive DTerm")
              (tcd
                   [| ( { Cmd =
                              BAnd
                                  [ bEq (BVar "foo") (BVar "bar")
                                    bEq (BVar "baz") (BNot (BVar "baz")) ]
                          WPre =
                              Multiset.ofFlatList
                                  [ gfunc (BVar "foo") "bar"
                                        [ Typed.Int (AVar "baz")
                                          Typed.Bool (BVar "fizz") ]
                                    gfunc (BGt (AVar "foobar", AVar "barbar")) "barbaz"
                                        [ Typed.Int
                                              (AAdd [ AVar "foobaz"; AVar "bazbaz" ]) ] ]
                          Goal =
                              (vfunc "bar"
                                   [ Typed.Int (AVar "baz")
                                     Typed.Bool (BVar "barbaz") ] : VFunc<Var> ) }
                       : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )
                      Context.negative |] )
                  .Returns(
                      ok <|
                      (Context.negative,
                       ( { Cmd =
                               BAnd
                                   [ bEq BTrue BTrue
                                     bEq BTrue (BNot BFalse) ]
                           WPre =
                               Multiset.ofFlatList
                                   [ gfunc BFalse "bar"
                                         [ Typed.Int (AInt 1L)
                                           Typed.Bool BTrue ]
                                     gfunc (BGt (AInt 0L, AInt 0L)) "barbaz"
                                         [ Typed.Int
                                               (AAdd [ AInt 1L; AInt 1L ]) ] ]
                           Goal =
                               (vfunc "bar"
                                    [ Typed.Int (AInt 0L)
                                      Typed.Bool BFalse ] : VFunc<Var> ) }
                        : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>> )))
                  .SetName("Successfully translate a negative DTerm") ]

        /// <summary>
        ///     Tests <c>subExprInDTerm</c> on positional substitutions.
        /// </summary>
        [<TestCaseSource("PositionSubExprInDTermCases")>]
        member this.testPositionSubExprInDTerm
          (t : Term<BoolExpr<Var>, GView<Var>, VFunc<Var>>)
          (pos : TraversalContext) =
            let trav = liftTraversalOverTerm positionTestSub
            let result = trav pos t
            okOption result
