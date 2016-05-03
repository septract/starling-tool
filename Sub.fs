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
    ///     The context of a substitution.
    /// </summary>
    type SubCtx =
        /// <summary>
        ///     No context: used for most substitutions.
        /// </summary>
        | NoCtx
        /// <summary>
        ///     A context for substitutions sensitive to whether a Boolean
        ///     expression is in positive or negative position.
        ///
        ///     <para>
        ///         This takes a stack of positions, so that traversal works
        ///         properly: nested expressions push onto the stack, then
        ///         pop back off it.
        ///     </para>
        /// </summary>
        | Positions of Position list
        override this.ToString () = sprintf "%A" this

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
            SubCtx,
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
            SubCtx,
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
        Mapper<SubCtx, 'srcVar, 'srcVar, IntExpr<'dstVar>, BoolExpr<'dstVar>>

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
            SubCtx,
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
    ///     If the context is position-based, push a new position onto
    ///     the position stack as a function of the current one.
    /// </summary>
    /// <param name="f">
    ///     The function transforming the position at the top of the stack.
    /// </param>
    /// <returns>
    ///     A function over a <c>SubCtx</c>.  If the context is not
    ///     <c>Positions</c>, it does not change the <c>SubCtx</c>; else,
    ///     it pushes a new position that is <c>f c</c>, where <c>c</c> is
    ///     the current position.
    /// </returns>
    let push (f : Position -> Position) : SubCtx -> SubCtx =
        function
        | Positions [] -> failwith "empty position stack"
        | Positions (x::xs) -> Positions ((f x)::x::xs)
        | x -> x

    /// <summary>
    ///     If the context is position-based, pop the position stack.
    /// </summary>
    /// <returns>
    ///     A function over a <c>SubCtx</c>.  If the context is not
    ///     <c>Positions</c>, it does not change the <c>SubCtx</c>; else,
    ///     it pops the current position.
    /// </returns>
    let pop : SubCtx -> SubCtx =
        function
        | Positions [] -> failwith "empty position stack"
        | Positions (x::xs) -> Positions xs
        | x -> x


/// <summary>
///     Functions for variable substitution.
/// </summary>
[<AutoOpen>]
module Var =
    /// Substitutes all variables with the given substitution function set
    /// for the given Boolean expression.
    let rec boolSubVars
      (vfun : VSubFun<'srcVar, 'dstVar>)
      (ctx : SubCtx) =
        function
        | BVar x -> Mapper.mapBoolCtx vfun (Position.push id ctx) x
        | BTrue -> (ctx, BTrue)
        | BFalse -> (ctx, BFalse)
        | BAnd xs ->
            let ctx', xs' = mapAccumL (Position.push id >> boolSubVars vfun) ctx xs
            (ctx', BAnd xs')
        | BOr xs ->
            let ctx', xs' = mapAccumL (Position.push id >> boolSubVars vfun) ctx xs
            (ctx', BOr xs')
        | BImplies (x, y) ->
            // The LHS of an implies is in negative ctxition.
            let ctxx, x' = boolSubVars vfun (Position.push Position.negate ctx) x
            let ctx', y' = boolSubVars vfun (Position.push id ctxx) y
            (ctx', BImplies (x', y'))
        | BEq (x, y) ->
            let ctxx, x' = Mapper.mapCtx (onVars vfun) (Position.push id ctx) x
            let ctx', y' = Mapper.mapCtx (onVars vfun) (Position.push id ctxx) y
            (ctx', BEq (x', y'))
        | BGt (x, y) ->
            let ctxx, x' = intSubVars vfun (Position.push id ctx) x
            let ctx', y' = intSubVars vfun (Position.push id ctxx) y
            (ctx', BGt (x', y'))
        | BGe (x, y) ->
            let ctxx, x' = intSubVars vfun (Position.push id ctx) x
            let ctx', y' = intSubVars vfun (Position.push id ctxx) y
            (ctx', BGe (x', y'))
        | BLe (x, y) ->
            let ctxx, x' = intSubVars vfun (Position.push id ctx) x
            let ctx', y' = intSubVars vfun (Position.push id ctxx) y
            (ctx', BLe (x', y'))
        | BLt (x, y) ->
            let ctxx, x' = intSubVars vfun (Position.push id ctx) x
            let ctx', y' = intSubVars vfun (Position.push id ctxx) y
            (ctx', BLt (x', y'))
        | BNot x ->
            let ctx', x' = boolSubVars vfun (Position.push Position.negate ctx) x
            (ctx', BNot x')
        >> pairMap Position.pop id

    /// Substitutes all variables with the given substitution function
    /// for the given arithmetic expression.
    and intSubVars
      (vfun : VSubFun<'srcVar, 'dstVar>)
      (ctx : SubCtx) =
        function
        | AVar x -> Mapper.mapIntCtx vfun (Position.push id ctx) x
        | AInt i -> (ctx, AInt i)
        | AAdd xs ->
            let ctx', xs' = mapAccumL (Position.push id >> intSubVars vfun) ctx xs
            (ctx', AAdd xs')
        | ASub xs ->
            let ctx', xs' = mapAccumL (Position.push id >> intSubVars vfun) ctx xs
            (ctx', ASub xs')
        | AMul xs ->
            let ctx', xs' = mapAccumL (Position.push id >> intSubVars vfun) ctx xs
            (ctx', AMul xs')
        | ADiv (x, y) ->
            let ctxx, x' = intSubVars vfun (Position.push id ctx) x
            let ctx', y' = intSubVars vfun (Position.push id ctxx) y
            (ctx', ADiv (x', y'))
        >> pairMap Position.pop id

    /// <summary>
    ///   Creates a <c>SubFun</c> from a <c>VSubFun</c>.
    /// </summary>
    and onVars vsub =
        Mapper.makeCtx (intSubVars vsub) (boolSubVars vsub)

    /// Failing form of boolSubVars.
    let rec tryBoolSubVars
      (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>)
      (ctx : SubCtx) =
        function
        | BVar x -> Mapper.mapBoolCtx vfun (Position.push id ctx) x
        | BTrue -> (ctx, ok BTrue)
        | BFalse -> (ctx, ok BFalse)
        | BAnd xs ->
            let ctx', xs' = mapAccumL (Position.push id >> tryBoolSubVars vfun) ctx xs
            (ctx', lift BAnd (collect xs'))
        | BOr xs ->
            let ctx', xs' = mapAccumL (Position.push id >> tryBoolSubVars vfun) ctx xs
            (ctx', lift BOr (collect xs'))
        | BImplies (x, y) ->
            // The LHS of an implies is in negative ctxition.
            let ctxx, x' = tryBoolSubVars vfun (Position.push Position.negate ctx) x
            let ctx', y' = tryBoolSubVars vfun (Position.push id ctxx) y
            (ctx', lift2 (curry BImplies) x' y')
        | BEq (x, y) ->
            let ctxx, x' = Mapper.tryMapCtx (tryOnVars vfun) (Position.push id ctx) x
            let ctx', y' = Mapper.tryMapCtx (tryOnVars vfun) (Position.push id ctxx) y
            (ctx', lift2 (curry BEq) x' y')
        | BGt (x, y) ->
            let ctxx, x' = tryIntSubVars vfun (Position.push id ctx) x
            let ctx', y' = tryIntSubVars vfun (Position.push id ctxx) y
            (ctx', lift2 (curry BGt) x' y')
        | BGe (x, y) ->
            let ctxx, x' = tryIntSubVars vfun (Position.push id ctx) x
            let ctx', y' = tryIntSubVars vfun (Position.push id ctxx) y
            (ctx', lift2 (curry BGe) x' y')
        | BLe (x, y) ->
            let ctxx, x' = tryIntSubVars vfun (Position.push id ctx) x
            let ctx', y' = tryIntSubVars vfun (Position.push id ctxx) y
            (ctx', lift2 (curry BLe) x' y')
        | BLt (x, y) ->
            let ctxx, x' = tryIntSubVars vfun (Position.push id ctx) x
            let ctx', y' = tryIntSubVars vfun (Position.push id ctxx) y
            (ctx', lift2 (curry BLt) x' y')
        | BNot x ->
            let ctx', x' = tryBoolSubVars vfun (Position.push Position.negate ctx) x
            (ctx', lift BNot x')

    /// Failing version of intSubVars.
    and tryIntSubVars
      (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>)
      (ctx : SubCtx) =
        function
        | AVar x -> Mapper.mapIntCtx vfun (Position.push id ctx) x
        | AInt i -> (ctx, ok (AInt i))
        | AAdd xs ->
            let ctx', xs' = mapAccumL (Position.push id >> tryIntSubVars vfun) ctx xs
            (ctx', lift AAdd (collect xs'))
        | ASub xs ->
            let ctx', xs' = mapAccumL (Position.push id >> tryIntSubVars vfun) ctx xs
            (ctx', lift ASub (collect xs'))
        | AMul xs ->
            let ctx', xs' = mapAccumL (Position.push id >> tryIntSubVars vfun) ctx xs
            (ctx', lift AMul (collect xs'))
        | ADiv (x, y) ->
            let ctxx, x' = tryIntSubVars vfun (Position.push id ctx) x
            let ctx', y' = tryIntSubVars vfun (Position.push id ctxx) y
            (ctx', lift2 (curry ADiv) x' y')

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
      (mapper : CMapper<SubCtx, 'srcVar, 'dstVar>)
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
      (mapper : CMapper<SubCtx, 'srcVar, 'dstVar>)
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
