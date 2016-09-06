/// <summary>
///     Functions for traversing and substituting expressions.
/// </summary>
module Starling.Core.Sub

open Chessie.ErrorHandling

open Starling.Utils
open Starling.Collections

open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr

/// <summary>
///     Types and functions for traversal context.
/// </summary>
[<AutoOpen>]
module Context =
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
    type TraversalContext =
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
    ///     A function over a <c>TraversalContext</c>.  If the context is not
    ///     <c>Positions</c>, it does not change the <c>TraversalContext</c>; else,
    ///     it pushes a new position that is <c>f c</c>, where <c>c</c> is
    ///     the current position.
    /// </returns>
    let push (f : Position -> Position) : TraversalContext -> TraversalContext =
        function
        | Positions [] -> failwith "empty position stack"
        | Positions (x::xs) -> Positions ((f x)::x::xs)
        | x -> x

    /// <summary>
    ///     If the context is position-based, pop the position stack.
    /// </summary>
    /// <returns>
    ///     A function over a <c>TraversalContext</c>.  If the context is not
    ///     <c>Positions</c>, it does not change the <c>TraversalContext</c>; else,
    ///     it pops the current position.
    /// </returns>
    let pop : TraversalContext -> TraversalContext =
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
    /// <typeparam name="Src">
    ///     The input type of <paramref name="g"/>, less the context.
    /// </typeparam>
    /// <typeparam name="Dst">
    ///     The return type of <paramref name="g"/>, less the context.
    /// </typeparam>
    /// <returns>
    ///     A function over a <c>TraversalContext</c>, which behaves as
    ///     <paramref name="g"/>, but, if the <c>TraversalContext</c> is
    ///     <c>Positions</c>, has pushed onto its incoming position stack
    ///     the result of calling <paramref name="f"/> on the current position.
    /// </returns>
    let changePos
      (f : Position -> Position)
      (g : TraversalContext -> 'Src -> Result<TraversalContext * 'Dst, 'Error>)
      (ctx : TraversalContext)
      : 'Src -> Result<TraversalContext * 'Dst, 'Error> =
        g (push f ctx) >> lift (pairMap pop id)

    /// <summary>
    ///     An initial positive position context.
    /// </summary>
    let positive : TraversalContext = Positions [Positive]

    /// <summary>
    ///     An initial negative position context.
    /// </summary>
    let negative : TraversalContext = Positions [Negative]


/// <summary>
///     A generic traversal.
/// </summary>
/// <typeparam name="Src">
///     The type of items before the traversal.
/// </typeparam>
/// <typeparam name="Dst">
///     The type of items after the traversal.
/// </typeparam>
/// <typeparam name="Error">
///     The type of errors that can occur during traversal.
/// </typeparam>
type Traversal<'Src, 'Dst, 'Error> =
    TraversalContext -> 'Src -> Result<TraversalContext * 'Dst, 'Error>

/// <summary>
///     Lifts a traversal to a context-less function.
/// </summary>
/// <param name="f">
///     The traversal to lift.
/// </param>
/// <typeparam name="Src">
///     The type of items before the traversal.
/// </typeparam>
/// <typeparam name="Dst">
///     The type of items after the traversal.
/// </typeparam>
/// <typeparam name="Error">
///     The type of errors that can occur during traversal.
/// </typeparam>
/// <returns>
///     The traversal <paramref name="f"/> lifted such that it accepts
///     <see cref="NoCtx"/> (and then discards it).
/// </returns>
let withoutContext
  (f : Traversal<'Src, 'Dst, 'Error>) : 'Src -> Result<'Dst, 'Error> =
    f NoCtx >> lift snd

/// <summary>
///     Lifts a function to a context-preserving traversal.
/// </summary>
/// <param name="f">
///     The function to lift.
/// </param>
/// <typeparam name="Src">
///     The type of items before the traversal.
/// </typeparam>
/// <typeparam name="Dst">
///     The type of items after the traversal.
/// </typeparam>
/// <typeparam name="Error">
///     The type of errors that can occur during traversal.
/// </typeparam>
/// <returns>
///     The function <paramref name="f"/> lifted such that it can be used
///     in a traversal.
/// </returns>
let ignoreContext
  (f : 'Src -> Result<'Dst, 'Error>) : Traversal<'Src, 'Dst, 'Error> =
    fun ctx -> f >> lift (mkPair ctx)

/// <summary>
///     Error type for variable substitutions.
/// </summary>
/// <typeparam name="Inner">
///     Type for errors returned by the traversal itself.
/// </typeparam>
type SubError<'Inner> =
    /// <summary>
    ///     An inner error occurred.
    /// </summary>
    | Inner of 'Inner
    /// <summary>
    ///     A type error occurred: the result of substitution was not the
    ///     appropriate type for the position in which it occurred.
    /// </summary>
    | BadType of expected : Type * got : Type
    /// <summary>
    ///     A substitution produced a context that wasn't expected.
    /// </summary>
    | ContextMismatch of expectedType : string * got : TraversalContext


/// <summary>
///     Tries to extract an <see cref="IntExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type.
/// </summary>
let expectInt : Expr<'Var> -> Result<IntExpr<'Var>, SubError<_>> =
    function
    | Int x -> ok x
    | tx -> fail (BadType (expected = Type.Int (), got = typeOf tx))

/// <summary>
///     Tries to extract an <see cref="BoolExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type.
/// </summary>
let expectBool : Expr<'Var> -> Result<BoolExpr<'Var>, SubError<_>> =
    function
    | Bool x -> ok x
    | tx -> fail (BadType (expected = Type.Bool (), got = typeOf tx))

// <summary>
//     Maps a traversal over an item, feeds the result into a function,
//     and returns the final context and the result of that function.
// </summary>
let tchain (f : Traversal<'A, 'AR, 'Error>) (g : 'AR -> 'Result)
  : Traversal<'A, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx -> f ctx >> lift (fun (ctxF, xR) -> ctxF, g xR)

// <summary>
//     Maps a traversal from left to right over a list, accumulating the
//     context, feeds the result list into a function, and returns the
//     final context and the result of that function.
// </summary>
let tchainL (f : Traversal<'A, 'AR, 'Error>) (g : 'AR list -> 'Result)
  : Traversal<'A list, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        seqBind
            (fun x (ctxN, xsRN) ->
                lift (fun (ctxS, xsRS) -> (ctxS, xsRS::xsRN))
                     (f ctxN x))
            (ctx, [])
        >> lift (pairMap id g)

// <summary>
//     Runs two traversals from left to right, accumulating the context,
//     feeds both results into a pair-accepting function, and returns the
//     final context and the result of that function.
// </summary>
let tchain2
  (f : Traversal<'A, 'AR, 'Error>)
  (g : Traversal<'B, 'BR, 'Error>)
  (h : ('AR * 'BR) -> 'Result)
  : Traversal<'A * 'B, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx (x, y) ->
        trial {
            let! ctxF, xR = f ctx x
            let! ctxG, yR = g ctxF y
            return (ctxG, h (xR, yR))
        }

/// <summary>
///     Lifts a variable substitution to one over Boolean expressions.
/// </summary>
let rec boolSubVars
    (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
    : Traversal<BoolExpr<'SrcVar>, BoolExpr<'DstVar>, SubError<'Error>> =
    // TODO(CaptainHayashi): proper doc comment.

    // We do some tricky inserting and removing of positions on the stack
    // to ensure the correct position appears in the correct place, and
    // is removed when we pop back up the expression stack.
    let bsv f = Context.changePos f (boolSubVars sub)
    let isv = Context.changePos id (intSubVars sub)
    let esv = Context.changePos id (exprSubVars sub)

    let neg = Context.negate

    fun ctx ->
        function
        | BVar x ->
            x
            |> CTyped.Bool
            |> Context.changePos id sub ctx
            |> mapMessages Inner
            |> bind (uncurry (ignoreContext expectBool))
        | BTrue -> ok (ctx, BTrue)
        | BFalse -> ok (ctx, BFalse)
        | BAnd xs -> tchainL (bsv id) BAnd ctx xs
        | BOr xs -> tchainL (bsv id) BOr ctx xs
        // The LHS of an implies is in negative position.
        | BImplies (x, y) -> tchain2 (bsv neg) (bsv id) BImplies ctx (x, y)
        | BEq (x, y) -> tchain2 esv esv BEq ctx (x, y)
        | BGt (x, y) -> tchain2 isv isv BGt ctx (x, y)
        | BGe (x, y) -> tchain2 isv isv BGe ctx (x, y)
        | BLe (x, y) -> tchain2 isv isv BLe ctx (x, y)
        | BLt (x, y) -> tchain2 isv isv BLt ctx (x, y)
        | BNot x -> tchain (bsv neg) BNot ctx x

/// Substitutes all variables with the given substitution function
/// for the given arithmetic expression.
and intSubVars
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<IntExpr<'SrcVar>, IntExpr<'DstVar>, SubError<'Error>> =
    let isv = Context.changePos id (intSubVars sub)
    // TODO(CaptainHayashi): proper doc comment.

    fun ctx ->
        function
        | AVar x ->
            x
            |> CTyped.Int
            |> Context.changePos id sub ctx
            |> mapMessages Inner
            |> bind (uncurry (ignoreContext expectInt))
        | AInt i -> ok (ctx, AInt i)
        | AAdd xs -> tchainL isv AAdd ctx xs
        | ASub xs -> tchainL isv ASub ctx xs
        | AMul xs -> tchainL isv AMul ctx xs
        | ADiv (x, y) -> tchain2 isv isv ADiv ctx (x, y)

/// <summary>
///   Creates an expression traversal from a variable traversal.
/// </summary>
and exprSubVars
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<Expr<'SrcVar>, Expr<'DstVar>, SubError<'Error>> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        function
        | Bool b -> b |> boolSubVars sub ctx |> lift (pairMap id Bool)
        | Int i -> i |> intSubVars sub ctx |> lift (pairMap id Int)

/// <summary>
///     Converts a traversal from variables to variables to one from
///     variables to expressions.
/// </summary>
/// <param name="sub">
///     The traversal to lift.
/// </param>
/// <typeparam name="SrcVar">
///     The type of variables entering the traversal.
/// </typeparam>
/// <typeparam name="DstVar">
///     The type of variables leaving the traversal.
/// </typeparam>
/// <returns>
///     <paramref name="mapper">, lifted into a <C>VSubFun</c>.
/// </returns>
let liftToExprDest
  (sub : Traversal<CTyped<'SrcVar>, CTyped<'DstVar>, 'Error>)
  : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error> =
    fun ctx -> sub ctx >> lift (pairMap id mkVarExp)

/// <summary>
///     Converts a non-symbolic expression to its pre-state.
/// </summary>
let vBefore (expr : Expr<Var>) : Result<Expr<MarkedVar>, SubError<'Error>> =
    ((mapCTyped Before >> ok)
    |> ignoreContext
    |> liftToExprDest
    |> exprSubVars
    |> withoutContext)
        expr

/// <summary>
///     Converts a non-symbolic expression to its post-state.
/// </summary>
let vAfter (expr : Expr<Var>) : Result<Expr<MarkedVar>, SubError<'Error>> =
    ((mapCTyped After >> ok)
    |> ignoreContext
    |> liftToExprDest
    |> exprSubVars
    |> withoutContext)
        expr

/// <summary>
///     Traversal for accumulating the <c>Var</c>s of an expression.
/// <summary>
let findVars : Traversal<Expr<Var>, Expr<Var>, SubError<'Error>>  =
    fun ctx ->
        let addVar =
            fun ctx v ->
                match ctx with
                | Vars vs -> ok (Vars (v::vs), v)
                | c -> ok (c, v)
        (addVar |> liftToExprDest |> exprSubVars) ctx

/// <summary>
///     Wrapper for running a <see cref="findVars"/>-style traversal
///     on a traversable construct.
/// <summary>
/// <param name="t">
///     The traversal to wrap.
/// </param>
/// <param name="subject">
///     The item in which to find vars.
/// </param>
/// <typeparam name="Subject">
///     The type of the item in which to find vars.
/// </typeparam>
/// <typeparam name="Errors">
///     The type of errors that can occur in the traversal.
/// </typeparam>
/// <returns>
///     The set of variables found in the expression.
/// </returns>
let mapOverVars
  (t : Traversal<'Subject, 'Subject, SubError<'Error>>)
  (subject : 'Subject)
  : Result<Set<CTyped<Var>>, SubError<'Error>> =
    subject
    |> t (Vars [])
    |> bind
        (function
         | (Vars xs, _) -> ok (Set.ofList xs)
         | (x, _) -> fail (ContextMismatch ("variable list", x)))

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
            expr |> mapOverVars findVars |> okOption
