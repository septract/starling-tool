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
        /// <summary>
        ///     A context for searching for <c>Var</c>s.
        /// </summary>
        | Vars of CTyped<Var> list
        /// <summary>
        ///     A context for searching for <c>MarkedVar</c>s.
        /// </summary>
        | MarkedVars of CTyped<MarkedVar> list
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
    type SubFun<'srcVar, 'dstVar>
      when 'srcVar : equality and 'dstVar : equality =
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
    type TrySubFun<'srcVar, 'dstVar, 'err>
      when 'srcVar : equality and 'dstVar : equality =
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
    type VSubFun<'srcVar, 'dstVar>
      when 'srcVar : equality and 'dstVar : equality =
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
    type VTrySubFun<'srcVar, 'dstVar, 'err>
      when 'srcVar : equality and 'dstVar : equality =
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
        | Positive -> BFalse
        | Negative -> BTrue

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
    ///     Wraps a context-sensitive function in a push and pop.
    /// </summary>
    /// <param name="f">
    ///     The function transforming the position at the top of the stack.
    /// </param>
    /// <param name="g">
    ///     The function, taking a context and item, to wrap; returns a pair of
    ///     context and another item.
    /// </param>
    /// <param name="ctx">
    ///     The current context.
    /// </param>
    /// <typeparam name="src">
    ///     The input type of <paramref name="g"/>, less the context.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The return type of <paramref name="g"/>, less the context.
    /// </typeparam>
    /// <returns>
    ///     A function over a <c>SubCtx</c>, which behaves as
    ///     <paramref name="g"/>, but, if the <c>SubCtx</c> is
    ///     <c>Positions</c>, has pushed onto its incoming position stack
    ///     the result of calling <paramref name="f"/> on the current position.
    /// </returns>
    let changePos
      (f : Position -> Position)
      (g : SubCtx -> 'src -> (SubCtx * 'item))
      (ctx : SubCtx)
      : ('src -> (SubCtx * 'item)) =
        g (push f ctx) >> pairMap pop id

    /// <summary>
    ///     An initial positive position context.
    /// </summary>
    let positive : SubCtx = Positions [Positive]

    /// <summary>
    ///     An initial negative position context.
    /// </summary>
    let negative : SubCtx = Positions [Negative]

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
        // We do some tricky inserting and removing of positions on the stack
        // to ensure the correct position appears in the correct place, and
        // is removed when we pop back up the expression stack.
        let bsv f = Position.changePos f (boolSubVars vfun)
        let isv f = Position.changePos f (intSubVars vfun)
        let esv f = Position.changePos f (Mapper.mapCtx (onVars vfun))

        function
        | BVar x ->
            Position.changePos id (Mapper.mapBoolCtx vfun) ctx x
        | BTrue -> (ctx, BTrue)
        | BFalse -> (ctx, BFalse)
        | BAnd xs ->
            let ctx', xs' = mapAccumL (bsv id) ctx xs
            (ctx', BAnd xs')
        | BOr xs ->
            let ctx', xs' = mapAccumL (bsv id) ctx xs
            (ctx', BOr xs')
        | BImplies (x, y) ->
            // The LHS of an implies is in negative position.
            let ctxx, x' = bsv Position.negate ctx x
            let ctx', y' = bsv id ctxx y
            (ctx', BImplies (x', y'))
        | BEq (x, y) ->
            let ctxx, x' = esv id ctx x
            let ctx', y' = esv id ctxx y
            (ctx', BEq (x', y'))
        | BGt (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', BGt (x', y'))
        | BGe (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', BGe (x', y'))
        | BLe (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', BLe (x', y'))
        | BLt (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', BLt (x', y'))
        | BNot x ->
            let ctx', x' = bsv Position.negate ctx x
            (ctx', BNot x')

    /// Substitutes all variables with the given substitution function
    /// for the given arithmetic expression.
    and intSubVars
      (vfun : VSubFun<'srcVar, 'dstVar>)
      (ctx : SubCtx) =
        let isv f = Position.changePos f (intSubVars vfun)

        function
        | AVar x ->
            Position.changePos id (Mapper.mapIntCtx vfun) ctx x
        | AInt i -> (ctx, AInt i)
        | AAdd xs ->
            let ctx', xs' = mapAccumL (isv id) ctx xs
            (ctx', AAdd xs')
        | ASub xs ->
            let ctx', xs' = mapAccumL (isv id) ctx xs
            (ctx', ASub xs')
        | AMul xs ->
            let ctx', xs' = mapAccumL (isv id) ctx xs
            (ctx', AMul xs')
        | ADiv (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', ADiv (x', y'))

    /// <summary>
    ///   Creates a <c>SubFun</c> from a <c>VSubFun</c>.
    /// </summary>
    and onVars vsub =
        Mapper.makeCtx (intSubVars vsub) (boolSubVars vsub)

    /// Failing form of boolSubVars.
    let rec tryBoolSubVars
      (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>)
      (ctx : SubCtx) =
        let bsv f = Position.changePos f (tryBoolSubVars vfun)
        let isv f = Position.changePos f (tryIntSubVars vfun)
        let esv f = Position.changePos f (Mapper.tryMapCtx (tryOnVars vfun))

        function
        | BVar x ->
            Position.changePos id (Mapper.mapBoolCtx vfun) ctx x
        | BTrue -> (ctx, ok BTrue)
        | BFalse -> (ctx, ok BFalse)
        | BAnd xs ->
            let ctx', xs' = mapAccumL (bsv id) ctx xs
            (ctx', lift BAnd (collect xs'))
        | BOr xs ->
            let ctx', xs' = mapAccumL (bsv id) ctx xs
            (ctx', lift BOr (collect xs'))
        | BImplies (x, y) ->
            // The LHS of an implies is in negative position.
            let ctxx, x' = bsv Position.negate ctx x
            let ctx', y' = bsv id ctxx y
            (ctx', lift2 (curry BImplies) x' y')
        | BEq (x, y) ->
            let ctxx, x' = esv id ctx x
            let ctx', y' = esv id ctxx y
            (ctx', lift2 (curry BEq) x' y')
        | BGt (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', lift2 (curry BGt) x' y')
        | BGe (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', lift2 (curry BGe) x' y')
        | BLe (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', lift2 (curry BLe) x' y')
        | BLt (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
            (ctx', lift2 (curry BLt) x' y')
        | BNot x ->
            let ctx', x' = bsv Position.negate ctx x
            (ctx', lift BNot x')

    /// Failing version of intSubVars.
    and tryIntSubVars
      (vfun : VTrySubFun<'srcVar, 'dstVar, 'err>)
      (ctx : SubCtx) =
        let isv f = Position.changePos f (tryIntSubVars vfun)

        function
        | AVar x ->
            Position.changePos id (Mapper.mapIntCtx vfun) ctx x
        | AInt i -> (ctx, ok (AInt i))
        | AAdd xs ->
            let ctx', xs' = mapAccumL (isv id) ctx xs
            let ctx', xs' = mapAccumL (Position.push id >> tryIntSubVars vfun) ctx xs
            (ctx', lift AAdd (collect xs'))
        | ASub xs ->
            let ctx', xs' = mapAccumL (isv id) ctx xs
            (ctx', lift ASub (collect xs'))
        | AMul xs ->
            let ctx', xs' = mapAccumL (isv id) ctx xs
            (ctx', lift AMul (collect xs'))
        | ADiv (x, y) ->
            let ctxx, x' = isv id ctx x
            let ctx', y' = isv id ctxx y
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
    ///     Substitution function for accumulating the <c>Var</c>s of an
    ///     expression.
    /// <summary>
    let findVars : SubFun<Var, Var> =
        Mapper.makeCtx
            (fun ctx x ->
                 match ctx with
                 | Vars xs -> (Vars ((Typed.Int x)::xs), AVar x)
                 | c -> (c, AVar x))
            (fun ctx x ->
                 match ctx with
                 | Vars xs -> (Vars ((Typed.Bool x)::xs), BVar x)
                 | c -> (c, BVar x))
        |> onVars

    /// <summary>
    ///     Wrapper for running a <see cref="findVars"/>-style function
    ///     on a sub-able construct.
    /// <summary>
    /// <param name="r">
    ///     The mapping function to wrap.
    /// </param>
    /// <param name="sf">
    ///     The substitution function to run.
    /// </param>
    /// <param name="subject">
    ///     The item in which to find vars.
    /// </param>
    /// <typeparam name="subject">
    ///     The type of the item in which to find vars.
    /// </typeparam>
    /// <returns>
    ///     The list of variables found in the expression.
    /// </returns>
    let mapOverVars
      (r : SubFun<Var, Var> -> SubCtx -> 'subject -> (SubCtx * 'subject))
      (sf : SubFun<Var, Var>)
      (subject : 'subject)
      : Set<CTyped<Var>> =
        match (r sf (Vars []) subject) with
        | (Vars xs, _) -> Set.ofList xs
        | _ -> failwith "mapOverVars: did not get Vars context back"

/// <summary>
///     Tests for <c>Sub</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Starling.Utils.Testing

    /// <summary>
    ///     NUnit tests for <c>Sub</c>.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for finding variables in expressions.
        /// </summary>
        static member FindVarsCases =
            [ (tcd
                   [| Expr.Bool (BTrue : VBoolExpr) |] )
                  .Returns(Set.empty)
                  .SetName("Finding vars in a Boolean primitive returns empty")
              (tcd
                   [| Expr.Int (AInt 1L : VIntExpr) |] )
                  .Returns(Set.empty)
                  .SetName("Finding vars in an integer primitive returns empty")
              (tcd
                   [| Expr.Bool (BVar "foo") |] )
                  .Returns(Set.singleton (CTyped.Bool "foo"))
                  .SetName("Finding vars in a Boolean var returns that var")
              (tcd
                   [| Expr.Int (AVar "bar") |] )
                  .Returns(Set.singleton (CTyped.Int "bar"))
                  .SetName("Finding vars in an integer var returns that var")
              (tcd
                   [| Expr.Bool
                          (BAnd
                               [ BOr
                                     [ BVar "foo"
                                       BVar "baz" ]
                                 BGt
                                     ( AVar "foobar",
                                       AVar "barbaz" ) ] ) |] )
                  .Returns(
                      Set.ofList
                          [ CTyped.Bool "foo"
                            CTyped.Bool "baz"
                            CTyped.Int "foobar"
                            CTyped.Int "barbaz" ])
                  .SetName("Finding vars in a Boolean expression works correctly")
              (tcd
                   [| Expr.Int
                         (AAdd
                              [ ASub
                                    [ AVar "foo"
                                      AVar "bar" ]
                                AMul
                                    [ AVar "foobar"
                                      AVar "barbaz" ]]) |])
                  .Returns(
                      Set.ofList
                          [ CTyped.Int "foo"
                            CTyped.Int "bar"
                            CTyped.Int "foobar"
                            CTyped.Int "barbaz" ])
                  .SetName("Finding vars in an integer expression works correctly") ]

        /// <summary>
        ///     Tests finding variables in expressions.
        /// </summary>
        [<TestCaseSource("FindVarsCases")>]
        member this.testFindVars expr =
            mapOverVars Mapper.mapCtx findVars expr
