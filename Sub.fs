/// <summary>
///     Functions for substituting expressions.
/// </summary>
module Starling.Core.Sub

open Chessie.ErrorHandling

open Starling.Utils
open Starling.Collections

open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr


/// <summary>
///     Types used in expression substitution.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A <c>Mapper</c> mapping between forms of <c>Expr</c>s.
    /// </summary>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    [<NoComparison>]
    [<NoEquality>]
    type SubFun<'srcVar, 'dstVar> =
        Mapper<
            IntExpr<'srcVar>, BoolExpr<'srcVar>,
            IntExpr<'dstVar>, BoolExpr<'dstVar>>

    /// <summary>
    ///     A possibly failing <c>Mapper</c> mapping between forms of <c>Expr</c>s.
    /// </summary>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of errors occurring in the map.
    /// </typeparam>
    [<NoComparison>]
    [<NoEquality>]
    type TrySubFun<'srcVar, 'dstVar, 'err> =
        Mapper<
            IntExpr<'srcVar>, BoolExpr<'srcVar>,
            Result<IntExpr<'dstVar>, 'err>,
            Result<BoolExpr<'dstVar>, 'err>>

    /// <summary>
    ///     A <c>Mapper</c> mapping between forms of <c>Var</c>s.
    /// </summary>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    [<NoComparison>]
    [<NoEquality>]
    type VSubFun<'srcVar, 'dstVar> =
        Mapper<'srcVar, 'srcVar, IntExpr<'dstVar>, BoolExpr<'dstVar>>

    /// <summary>
    ///     A <c>TypeMap</c> partially mapping between forms of <c>Var</c>s.
    /// </summary>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of errors if the map fails.
    /// </typeparam>
    [<NoComparison>]
    [<NoEquality>]
    type VTrySubFun<'srcVar, 'dstVar, 'err> =
        Mapper<
            'srcVar, 'srcVar,
            Result<IntExpr<'dstVar>, 'err>,
            Result<BoolExpr<'dstVar>, 'err>>


(*
 * Variable substitution (special case of substitution)
 *)

/// Substitutes all variables with the given substitution function set
/// for the given Boolean expression.
let rec boolSubVars (vfun : VSubFun<'srcVar, 'dstVar>) =
    function
    | BVar x -> Mapper.mapBool vfun x
    | BTrue -> BTrue
    | BFalse -> BFalse
    | BAnd xs -> BAnd (List.map (boolSubVars vfun) xs)
    | BOr xs -> BOr (List.map (boolSubVars vfun) xs)
    | BImplies (x, y) -> BImplies (boolSubVars vfun x,
                                   boolSubVars vfun y)
    | BEq (x, y) -> BEq (Mapper.map (onVars vfun) x,
                         Mapper.map (onVars vfun) y)
    | BGt (x, y) -> BGt (intSubVars vfun x,
                         intSubVars vfun y)
    | BGe (x, y) -> BGe (intSubVars vfun x,
                         intSubVars vfun y)
    | BLe (x, y) -> BLe (intSubVars vfun x,
                         intSubVars vfun y)
    | BLt (x, y) -> BLt (intSubVars vfun x,
                         intSubVars vfun y)
    | BNot x -> BNot (boolSubVars vfun x)

/// Substitutes all variables with the given substitution function
/// for the given arithmetic expression.
and intSubVars (vfun : VSubFun<'srcVar, 'dstVar>) =
    function
    | AVar x -> Mapper.mapInt vfun x
    | AInt i -> AInt i
    | AAdd xs -> AAdd (List.map (intSubVars vfun) xs)
    | ASub xs -> ASub (List.map (intSubVars vfun) xs)
    | AMul xs -> AMul (List.map (intSubVars vfun) xs)
    | ADiv (x, y) -> ADiv (intSubVars vfun x,
                           intSubVars vfun y)

/// <summary>
///   Creates a <c>SubFun</c> from a <c>VSubFun</c>.
/// </summary>
and onVars vsub =
    Mapper.make (intSubVars vsub) (boolSubVars vsub)

/// Failing form of boolSubVars.
let rec tryBoolSubVars (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>) =
    function
    | BVar x -> Mapper.mapBool vfun x
    | BTrue -> ok BTrue
    | BFalse -> ok BFalse
    | BAnd xs ->
        xs |> List.map (tryBoolSubVars vfun) |> collect |> lift BAnd
    | BOr xs ->
        xs |> List.map (tryBoolSubVars vfun) |> collect |> lift BOr
    | BImplies (x, y) ->
        lift2
            (curry BImplies)
            (tryBoolSubVars vfun x)
            (tryBoolSubVars vfun y)
    | BEq (x, y) ->
        lift2
            (curry BEq)
            (Mapper.tryMap (tryOnVars vfun) x)
            (Mapper.tryMap (tryOnVars vfun) y)
    | BGt (x, y) ->
        lift2
            (curry BGt)
            (tryIntSubVars vfun x)
            (tryIntSubVars vfun y)
    | BGe (x, y) ->
        lift2
            (curry BGe)
            (tryIntSubVars vfun x)
            (tryIntSubVars vfun y)
    | BLe (x, y) ->
        lift2
            (curry BLe)
            (tryIntSubVars vfun x)
            (tryIntSubVars vfun y)
    | BLt (x, y) ->
        lift2
            (curry BLt)
            (tryIntSubVars vfun x)
            (tryIntSubVars vfun y)
    | BNot x ->
        x |> tryBoolSubVars vfun |> lift BNot

/// Failing version of intSubVars.
and tryIntSubVars (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>) =
    function
    | AVar x -> Mapper.mapInt vfun x
    | AInt i -> i |> AInt |> ok
    | AAdd xs ->
        xs
        |> List.map (tryIntSubVars vfun)
        |> collect
        |> lift AAdd
    | ASub xs ->
        xs
        |> List.map (tryIntSubVars vfun)
        |> collect
        |> lift ASub
    | AMul xs ->
        xs
        |> List.map (tryIntSubVars vfun)
        |> collect
        |> lift AMul
    | ADiv (x, y) ->
        lift2
            (curry ADiv)
            (tryIntSubVars vfun x)
            (tryIntSubVars vfun y)

/// <summary>
///   Creates a <c>TrySubFun</c> from a <c>VTrySubFun</c>.
/// </summary>
and tryOnVars
  (vsub : VTrySubFun<'srcVar, 'dstVar, 'err>) =
    Mapper.make (tryIntSubVars vsub) (tryBoolSubVars vsub)


(*
 * Variable marking (special case of variable substitution)
 *)

/// Lifts a VSubFun so it returns expressions.
let liftVSubFun vsf =
    Mapper.compose vsf (Mapper.make AVar BVar)

/// Converts a non-symbolic expression to its pre-state.
let vBefore
  : SubFun<Var, MarkedVar> =
    Before
    |> Mapper.cmake
    |> liftVSubFun
    |> onVars

/// Converts a non-symbolic expression to its post-state.
let vAfter
  : SubFun<Var, MarkedVar> =
    After
    |> Mapper.cmake
    |> liftVSubFun
    |> onVars


/// <summary>
///     Tests for <c>Sub</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Starling.Utils.Testing

    // TODO(CaptainHayashi): put tests here.
