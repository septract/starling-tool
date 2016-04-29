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
    ///     Enumeration of positions of a Boolean expression.
    ///
    ///     <para>
    ///         An expression starts in positive position, and flips position
    ///         whenever it passes through a negation, or the LHS of an
    ///         implication.
    ///     </para>
    /// </summary>
    type Position =
        /// <summary>
        ///     Positive position: over-approximations are <c>false</c>.
        /// </summary>
        | Positive
        /// <summary>
        ///     Negative position: over-approximations are <c>true</c>.
        /// </summary>
        | Negative

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
            Position,
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
            Position,
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
        Mapper<Position, 'srcVar, 'srcVar, IntExpr<'dstVar>, BoolExpr<'dstVar>>

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
            Position,
            'srcVar, 'srcVar,
            Result<IntExpr<'dstVar>, 'err>,
            Result<BoolExpr<'dstVar>, 'err>>


/// <summary>
///     Functions for Boolean positions.
/// </summary>
module Position =
    /// <summary>
    ///     Negates a Boolean position.
    /// </summary>
    let negate : Position -> Position =
        function
        | Positive -> Negative
        | Negative -> Positive

    /// <summary>
    ///     Produces the correct over-approximation for a Boolean position.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the <c>BoolExpr</c> returned.
    /// </typeparam>
    let overapprox : Position -> BoolExpr<'var> =
        function
        | Positive -> BTrue
        | Negative -> BFalse

    /// <summary>
    ///     Produces the correct under-approximation for a Boolean position.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the <c>BoolExpr</c> returned.
    /// </typeparam>
    let underapprox : Position -> BoolExpr<'var> =
        function
        | Positive -> BTrue
        | Negative -> BFalse


/// <summary>
///     Functions for variable substitution.
/// </summary>
[<AutoOpen>]
module Var =
    /// Substitutes all variables with the given substitution function set
    /// for the given Boolean expression.
    let rec boolSubVars
      (vfun : VSubFun<'srcVar, 'dstVar>)
      (pos : Position) =
        function
        | BVar x -> Mapper.mapBoolCtx vfun pos x
        | BTrue -> (pos, BTrue)
        | BFalse -> (pos, BFalse)
        | BAnd xs ->
            let pos', xs' = mapAccumL (boolSubVars vfun) pos xs
            (pos', BAnd xs')
        | BOr xs ->
            let pos', xs' = mapAccumL (boolSubVars vfun) pos xs
            (pos', BOr xs')
        | BImplies (x, y) ->
            // The LHS of an implies is in negative position.
            let posx, x' = boolSubVars vfun (Position.negate pos) x
            let pos', y' = boolSubVars vfun pos y
            (pos', BImplies (x', y'))
        | BEq (x, y) ->
            let posx, x' = Mapper.mapCtx (onVars vfun) pos x
            let pos', y' = Mapper.mapCtx (onVars vfun) pos y
            (pos', BEq (x', y'))
        | BGt (x, y) ->
            let posx, x' = intSubVars vfun pos x
            let pos', y' = intSubVars vfun pos y
            (pos', BGt (x', y'))
        | BGe (x, y) ->
            let posx, x' = intSubVars vfun pos x
            let pos', y' = intSubVars vfun pos y
            (pos', BGe (x', y'))
        | BLe (x, y) ->
            let posx, x' = intSubVars vfun pos x
            let pos', y' = intSubVars vfun pos y
            (pos', BLe (x', y'))
        | BLt (x, y) ->
            let posx, x' = intSubVars vfun pos x
            let pos', y' = intSubVars vfun pos y
            (pos', BLt (x', y'))
        | BNot x ->
            let pos', x' = boolSubVars vfun (Position.negate pos) x
            (pos', BNot x')

    /// Substitutes all variables with the given substitution function
    /// for the given arithmetic expression.
    and intSubVars
      (vfun : VSubFun<'srcVar, 'dstVar>)
      (pos : Position) =
        function
        | AVar x -> Mapper.mapIntCtx vfun pos x
        | AInt i -> (pos, AInt i)
        | AAdd xs ->
            let pos', xs' = mapAccumL (intSubVars vfun) pos xs
            (pos', AAdd xs')
        | ASub xs ->
            let pos', xs' = mapAccumL (intSubVars vfun) pos xs
            (pos', ASub xs')
        | AMul xs ->
            let pos', xs' = mapAccumL (intSubVars vfun) pos xs
            (pos', AMul xs')
        | ADiv (x, y) ->
            let posx, x' = intSubVars vfun pos x
            let pos', y' = intSubVars vfun pos y
            (pos', ADiv (x', y'))

    /// <summary>
    ///   Creates a <c>SubFun</c> from a <c>VSubFun</c>.
    /// </summary>
    and onVars vsub =
        Mapper.makeCtx (intSubVars vsub) (boolSubVars vsub)

    /// Failing form of boolSubVars.
    let rec tryBoolSubVars
      (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>)
      (pos : Position) =
        function
        | BVar x -> Mapper.mapBoolCtx vfun pos x
        | BTrue -> (pos, ok BTrue)
        | BFalse -> (pos, ok BFalse)
        | BAnd xs ->
            let pos', xs' = mapAccumL (tryBoolSubVars vfun) pos xs
            (pos', lift BAnd (collect xs'))
        | BOr xs ->
            let pos', xs' = mapAccumL (tryBoolSubVars vfun) pos xs
            (pos', lift BOr (collect xs'))
        | BImplies (x, y) ->
            // The LHS of an implies is in negative position.
            let posx, x' = tryBoolSubVars vfun (Position.negate pos) x
            let pos', y' = tryBoolSubVars vfun pos y
            (pos', lift2 (curry BImplies) x' y')
        | BEq (x, y) ->
            let posx, x' = Mapper.tryMapCtx (tryOnVars vfun) pos x
            let pos', y' = Mapper.tryMapCtx (tryOnVars vfun) pos y
            (pos', lift2 (curry BEq) x' y')
        | BGt (x, y) ->
            let posx, x' = tryIntSubVars vfun pos x
            let pos', y' = tryIntSubVars vfun pos y
            (pos', lift2 (curry BGt) x' y')
        | BGe (x, y) ->
            let posx, x' = tryIntSubVars vfun pos x
            let pos', y' = tryIntSubVars vfun pos y
            (pos', lift2 (curry BGe) x' y')
        | BLe (x, y) ->
            let posx, x' = tryIntSubVars vfun pos x
            let pos', y' = tryIntSubVars vfun pos y
            (pos', lift2 (curry BLe) x' y')
        | BLt (x, y) ->
            let posx, x' = tryIntSubVars vfun pos x
            let pos', y' = tryIntSubVars vfun pos y
            (pos', lift2 (curry BLt) x' y')
        | BNot x ->
            let pos', x' = tryBoolSubVars vfun (Position.negate pos) x
            (pos', lift BNot x')

    /// Failing version of intSubVars.
    and tryIntSubVars
      (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>)
      (pos : Position) =
        function
        | AVar x -> Mapper.mapIntCtx vfun pos x
        | AInt i -> (pos, ok (AInt i))
        | AAdd xs ->
            let pos', xs' = mapAccumL (tryIntSubVars vfun) pos xs
            (pos', lift AAdd (collect xs'))
        | ASub xs ->
            let pos', xs' = mapAccumL (tryIntSubVars vfun) pos xs
            (pos', lift ASub (collect xs'))
        | AMul xs ->
            let pos', xs' = mapAccumL (tryIntSubVars vfun) pos xs
            (pos', lift AMul (collect xs'))
        | ADiv (x, y) ->
            let posx, x' = tryIntSubVars vfun pos x
            let pos', y' = tryIntSubVars vfun pos y
            (pos', lift2 (curry ADiv) x' y')

    /// <summary>
    ///   Creates a <c>TrySubFun</c> from a <c>VTrySubFun</c>.
    /// </summary>
    and tryOnVars
      (vsub : VTrySubFun<'srcVar, 'dstVar, 'err>) =
        Mapper.makeCtx (tryIntSubVars vsub) (tryBoolSubVars vsub)

    /// <summary>
    ///     Converts a <c>CMapper</c> on variables to a <c>VSubFun</c>.
    /// </summary>
    /// <param name="mapper">
    ///     The variable <c>CMapper</c> to lift.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <returns>
    ///     <paramref name="mapper">, lifted into a <C>VSubFun</c>.
    /// </returns>
    let liftCToVSub
      (mapper : CMapper<Position, 'srcVar, 'dstVar>)
      : VSubFun<'srcVar, 'dstVar> =
        Mapper.compose mapper (Mapper.make AVar BVar)

    /// <summary>
    ///     Converts a <c>CMapper</c> on variables to a <c>SubFun</c>.
    /// </summary>
    /// <param name="mapper">
    ///     The variable <c>CMapper</c> to lift.
    /// </param>
    /// <typeparam name="srcVar">
    ///     The type of variables entering the map.
    /// </typeparam>
    /// <typeparam name="dstVar">
    ///     The type of variables leaving the map.
    /// </typeparam>
    /// <returns>
    ///     <paramref name="mapper">, lifted into a <C>SubFun</c>.
    /// </returns>
    let liftCToSub
      (mapper : CMapper<Position, 'srcVar, 'dstVar>)
      : SubFun<'srcVar, 'dstVar> =
        mapper |> liftCToVSub |> onVars

    /// <summary>
    ///     Converts a non-symbolic expression to its pre-state.
    /// </summary>
    let vBefore
      : SubFun<Var, MarkedVar> =
        Before |> Mapper.cmake |> liftCToSub

    /// <summary>
    ///     Converts a non-symbolic expression to its post-state.
    /// </summary>
    let vAfter
      : SubFun<Var, MarkedVar> =
        After |> Mapper.cmake |> liftCToSub


/// <summary>
///     Tests for <c>Sub</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Starling.Utils.Testing

    // TODO(CaptainHayashi): put tests here.
