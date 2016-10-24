/// <summary>
///     Functions for traversing and substituting expressions.
///
///     <para>
///         This module defines <see cref="Traversal"/>, the type of functions
///         that can be distributed over expressions, views, and other
///         constructs using traversal combinators.  Traversals are
///         map-accumulates that build up a <see cref="TraversalContext"/>
///         while visiting variables in a traversable structure.
///     </para>
/// </summary>
module Starling.Core.Traversal

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
///     Error type for variable substitutions.
/// </summary>
/// <typeparam name="Inner">
///     Type for errors returned by the traversal itself.
/// </typeparam>
type TraversalError<'Inner> =
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
///     A generic traversal.
/// </summary>
/// <typeparam name="Src">
///     The type of items before the traversal.
/// </typeparam>
/// <typeparam name="Dst">
///     The type of items after the traversal.
/// </typeparam>
/// <typeparam name="Error">
///     The type of inner errors that can occur during traversal.
/// </typeparam>
type Traversal<'Src, 'Dst, 'Error> =
    TraversalContext -> 'Src ->
        Result<TraversalContext * 'Dst, TraversalError<'Error>>

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
let mapTraversal
  (f : Traversal<'Src, 'Dst, 'Error>) : 'Src -> Result<'Dst, TraversalError<'Error>> =
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
  (f : 'Src -> Result<'Dst, TraversalError<'Error>>) : Traversal<'Src, 'Dst, 'Error> =
    fun ctx -> f >> lift (mkPair ctx)

/// <summary>
///     Allows a context-less function to be lifted by traversal lifter
///     functions.
///
///     <para>
///         This allows, for example, simple functions from one variable type
///         to another to be converted into functions over expressions by using
///         <see cref="tliftOverExpr"/> as <paramref name="lifter"/>.
///     </para>
/// </summary>
/// <param name="f">The function to lift.</param>
/// <param name="lift">The traversal lifter to use.</param>
/// <typeparam name="SrcA">
///     The type of items before the original function.
/// </typeparam>
/// <typeparam name="DstA">
///     The type of items after the original function.
/// </typeparam>
/// <typeparam name="ErrorA">
///     The type of errors that can occur during the original function.
/// </typeparam>
/// <typeparam name="SrcB">
///     The type of items before the lifted function.
/// </typeparam>
/// <typeparam name="DstB">
///     The type of items after the lifted function.
/// </typeparam>
/// <typeparam name="ErrorB">
///     The type of errors that can occur during the lifted function, to be
///     wrapped in <see cref="TraversalError"/>.
/// </typeparam>
/// <returns>
///     The function <paramref name="f"/> lifted over <paramref name="lift"/>.
/// </returns>
let liftWithoutContext
  (f : 'SrcA -> Result<'DstA, 'ErrorA>)
  (lift : Traversal<'SrcA, 'DstA, 'ErrorA> -> Traversal<'SrcB, 'DstB, 'ErrorB>)
  : 'SrcB -> Result<'DstB, TraversalError<'ErrorB>> =
    mapTraversal (lift (ignoreContext (f >> mapMessages Inner)))

/// <summary>
///     Lifts a traversal over <see cref="CTyped"/>.
/// </summary>
let tliftOverCTyped
  (sub : Traversal<'Src, 'Dest, 'Error>)
  : Traversal<CTyped<'Src>, CTyped<'Dest>, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        function
        | Int i -> lift (pairMap id Int) (sub ctx i)
        | Bool b -> lift (pairMap id Bool) (sub ctx b)
        | Array (eltype, length, a) ->
            lift (pairMap id (fun a -> Array (eltype, length, a))) (sub ctx a)

/// <summary>
///     Tries to extract an <see cref="ArrayExpr"/> out of an
///     <see cref="ArrayExpr"/>, failing if the expression is not of that type
///     or the element type or array is wrong.
/// </summary>
let expectArray
  (eltype : Type)
  (length : int option)
  (expr : Expr<'Var>)
  : Result<ArrayExpr<'Var>, TraversalError<_>> =
    // TODO(CaptainHayashi): proper doc comment.
    match expr with
    | Typed.Array (_, _, ae)
        when typesCompatible (Type.Array (eltype, length, ())) (typeOf expr) ->
        ok ae
    | _ ->
        fail
            (BadType
                (expected = Type.Array (eltype, length, ()), got = typeOf expr))

/// <summary>
///     Tries to extract an <see cref="IntExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type.
/// </summary>
let expectInt : Expr<'Var> -> Result<IntExpr<'Var>, TraversalError<_>> =
    // TODO(CaptainHayashi): proper doc comment.
    function
    | Int x -> ok x
    | tx -> fail (BadType (expected = Type.Int (), got = typeOf tx))

/// <summary>
///     Tries to extract an <see cref="BoolExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type.
/// </summary>
let expectBool : Expr<'Var> -> Result<BoolExpr<'Var>, TraversalError<_>> =
    // TODO(CaptainHayashi): proper doc comment.
    function
    | Bool x -> ok x
    | tx -> fail (BadType (expected = Type.Bool (), got = typeOf tx))

/// <summary>
///     Maps a traversal over an item, feeds the result into a function,
///     and returns the final context and the result of that function.
/// </summary>
let tchain (f : Traversal<'A, 'AR, 'Error>) (g : 'AR -> 'Result)
  : Traversal<'A, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx -> f ctx >> lift (fun (ctxF, xR) -> ctxF, g xR)

/// <summary>
///     Maps a traversal from left to right over a list, accumulating the
///     context, feeds the result list into a function, and returns the
///     final context and the result of that function.
/// </summary>
let tchainL (f : Traversal<'A, 'AR, 'Error>) (g : 'AR list -> 'Result)
  : Traversal<'A list, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        seqBind
            (fun x (ctxN, xsRN) ->
                lift (fun (ctxS, xsRS) -> (ctxS, xsRS::xsRN))
                     (f ctxN x))
            (ctx, [])
        >> lift (pairMap id (List.rev >> g))

/// <summary>
///     Maps a traversal from left to right over a multiset, accumulating the
///     context; feeds the result list into a functionl and returns the
///     final context and the result of that function.
///     <para>
///         The context is only updated once for each unique item in the
///         multiset.
///     </para>
/// </summary>
let tchainM (f : Traversal<'A, 'AR, 'Error>) (g : Multiset<'AR> -> 'Result)
  : Traversal<Multiset<'A>, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    let trav ctx ms =
        let ms' =
            Multiset.fold
                (fun res x n ->
                    trial {
                        let! (c, mset) = res
                        let! (c', x') = f c x
                        return (c', Multiset.addn mset x' n)
                    })
                (ok (ctx, Multiset.empty))
                ms
        lift (pairMap id g) ms'
    trav

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

// <summary>
//     Runs three traversals from left to right, accumulating the context,
//     feeds both results into a triple-accepting function, and returns the
//     final context and the result of that function.
// </summary>
let tchain3
  (f : Traversal<'A, 'AR, 'Error>)
  (g : Traversal<'B, 'BR, 'Error>)
  (h : Traversal<'C, 'CR, 'Error>)
  (i : ('AR * 'BR * 'CR) -> 'Result)
  : Traversal<'A * 'B * 'C, 'Result, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx (x, y, z) ->
        trial {
            let! ctxF, xR = f ctx x
            let! ctxG, yR = g ctxF y
            let! ctxH, zR = h ctxG z
            return (ctxH, i (xR, yR, zR))
        }

/// <summary>
///     Converts a traversal from typed variables to expressions to one from
///     Boolean expressions to Boolean expressions.
/// </summary>
let rec tLiftToBoolSrc
    (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
    : Traversal<BoolExpr<'SrcVar>, BoolExpr<'DstVar>, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.

    // We do some tricky inserting and removing of positions on the stack
    // to ensure the correct position appears in the correct place, and
    // is removed when we pop back up the expression stack.
    let bsv f x = Context.changePos f (tLiftToBoolSrc sub) x
    let isv x = Context.changePos id (tLiftToIntSrc sub) x
    let esv x = Context.changePos id (tliftToExprSrc sub) x

    let neg = Context.negate

    fun ctx ->
        function
        | BVar x ->
            x
            |> CTyped.Bool
            |> Context.changePos id sub ctx
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

/// <summary>
///     Converts a traversal from typed variables to expressions to one from
///     integral expressions to integral expressions.
/// </summary>
and tLiftToIntSrc
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<IntExpr<'SrcVar>, IntExpr<'DstVar>, 'Error> =
    let isv x = Context.changePos id (tLiftToIntSrc sub) x
    // TODO(CaptainHayashi): proper doc comment.

    fun ctx ->
        function
        | IVar x ->
            x
            |> CTyped.Int
            |> Context.changePos id sub ctx
            |> bind (uncurry (ignoreContext expectInt))
        | IInt i -> ok (ctx, IInt i)
        | IAdd xs -> tchainL isv IAdd ctx xs
        | ISub xs -> tchainL isv ISub ctx xs
        | IMul xs -> tchainL isv IMul ctx xs
        | IDiv (x, y) -> tchain2 isv isv IDiv ctx (x, y)
        | IMod (x, y) -> tchain2 isv isv IMod ctx (x, y)

/// <summary>
///     Converts a traversal from typed variables to expressions to one from
///     array expressions to array expressions.
/// </summary>
and tLiftToArraySrc
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<(Type * int option * ArrayExpr<'SrcVar>),
              (Type * int option * ArrayExpr<'DstVar>), 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx (eltype, length, arrayExpr) ->
        let arrayExprResult =
            match arrayExpr with
            | AVar x ->
                let typedVar = CTyped.Array (eltype, length, x)
                let exprResult = Context.changePos id sub ctx typedVar
                (* Traversals have to preserve the element type and, if it
                   exists, the length. *)
                bind
                    (uncurry (ignoreContext (expectArray eltype length)))
                    exprResult
        lift (fun (ctx, ex) -> (ctx, (eltype, length, ex))) arrayExprResult

and tliftToExprSrc
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        function
        | Bool b -> b |> tLiftToBoolSrc sub ctx |> lift (pairMap id Bool)
        | Int i -> i |> tLiftToIntSrc sub ctx |> lift (pairMap id Int)
        | Array (eltype, length, a) ->
            lift
                (fun (ctx', ela) -> (ctx', Array ela))
                (tLiftToArraySrc sub ctx (eltype, length, a))

/// <summary>
///     Adapts an expression traversal to work on Boolean expressions.
///     Fails if the traversal responds with a non-Boolean expression.
/// </summary>
let traverseBoolAsExpr
  (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<BoolExpr<'SrcVar>, BoolExpr<'DstVar>, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    let toExpr = ignoreContext (Bool >> ok)
    let fromExpr = ignoreContext expectBool
    fun ctx expr -> toExpr ctx expr >>= uncurry traversal >>= uncurry fromExpr

/// <summary>
///     Adapts an expression traversal to work on integer expressions.
///     Fails if the traversal responds with a non-integer expression.
/// </summary>
let traverseIntAsExpr
  (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error>)
  : Traversal<IntExpr<'SrcVar>, IntExpr<'DstVar>, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    let toExpr = ignoreContext (Int >> ok)
    let fromExpr = ignoreContext expectInt
    fun ctx expr -> toExpr ctx expr >>= uncurry traversal >>= uncurry fromExpr

/// <summary>
///     Converts a traversal from typed variables to typed variables to one from
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
///     <paramref name="sub">, lifted to return expressions.
/// </returns>
let tliftToExprDest
  (sub : Traversal<CTyped<'SrcVar>, CTyped<'DstVar>, 'Error>)
  : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error> =
    fun ctx -> sub ctx >> lift (pairMap id mkVarExp)

/// <summary>
///     Converts a traversal from typed variables to typed variables to one from
///     expressions to expressions.
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
///     <paramref name="sub">, lifted over expressions.
/// </returns>
let tliftOverExpr
  (sub : Traversal<CTyped<'SrcVar>, CTyped<'DstVar>, 'Error>)
  : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error> =
    sub |> tliftToExprDest |> tliftToExprSrc

/// <summary>
///     Converts a non-symbolic expression to its pre-state.
/// </summary>
let vBefore (expr : Expr<Var>) : Result<Expr<MarkedVar>, TraversalError<'Error>> =
    // TODO(CaptainHayashi): proper doc comment.
    ((Before >> ok)
    |> ignoreContext
    |> tliftOverCTyped
    |> tliftOverExpr
    |> mapTraversal)
        expr

/// <summary>
///     Converts a non-symbolic expression to its post-state.
/// </summary>
let vAfter (expr : Expr<Var>) : Result<Expr<MarkedVar>, TraversalError<'Error>> =
    // TODO(CaptainHayashi): proper doc comment.
    ((After >> ok)
    |> ignoreContext
    |> tliftOverCTyped
    |> tliftOverExpr
    |> mapTraversal)
        expr

/// <summary>
///     Updates a context with a new variable.
/// <summary>
let pushVar (ctx : TraversalContext) (v : TypedVar)
  : Result<TraversalContext, TraversalError<'Error>>=
    // TODO(CaptainHayashi): proper doc comment.
    match ctx with
    | Vars vs -> ok (Vars (v::vs))
    | c -> fail (ContextMismatch ("vars context", c))

/// <summary>
///     Traversal for accumulating <c>Var</c>s.
/// <summary>
let collectVars : Traversal<TypedVar, TypedVar, 'Error>  =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx v -> lift (fun ctx -> (ctx, v)) (pushVar ctx v)

/// <summary>
///     Updates a context with a new marked variable.
/// <summary>
let pushMarkedVar (ctx : TraversalContext) (v : CTyped<MarkedVar>)
  : Result<TraversalContext, TraversalError<'Error>> =
    // TODO(CaptainHayashi): proper doc comment.
    match ctx with
    | MarkedVars vs -> ok (MarkedVars (v::vs))
    | c -> fail (ContextMismatch ("markedvars context", c))

/// <summary>
///     Traversal for accumulating <c>MarkedVar</c>s.
/// <summary>
let collectMarkedVars
  : Traversal<CTyped<MarkedVar>, CTyped<MarkedVar>, 'Error> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx v -> lift (fun ctx -> (ctx, v)) (pushMarkedVar ctx v)

/// <summary>
///     Wrapper for running a <see cref="collectVars"/>-style traversal
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
let findVars
  (t : Traversal<'Subject, 'Subject, 'Error>)
  (subject : 'Subject)
  : Result<Set<CTyped<Var>>, TraversalError<'Error>> =
    subject
    |> t (Vars [])
    |> bind
        (function
         | (Vars xs, _) -> ok (Set.ofList xs)
         | (x, _) -> fail (ContextMismatch ("variable list", x)))

/// <summary>
///     Wrapper for running a <see cref="collectMarkedVars"/>-style traversal
///     on a traversable construct.
/// <summary>
/// <param name="t">
///     The traversal to wrap.
/// </param>
/// <param name="subject">
///     The item in which to find marked vars.
/// </param>
/// <typeparam name="Subject">
///     The type of the item in which to find marked vars.
/// </typeparam>
/// <typeparam name="Errors">
///     The type of errors that can occur in the traversal.
/// </typeparam>
/// <returns>
///     The set of variables found in the expression.
/// </returns>
let findMarkedVars
  (t : Traversal<'Subject, 'Subject, 'Error>)
  (subject : 'Subject)
  : Result<Set<CTyped<MarkedVar>>, TraversalError<'Error>> =
    subject
    |> t (MarkedVars [])
    |> bind
        (function
         | (MarkedVars xs, _) -> ok (Set.ofList xs)
         | (x, _) -> fail (ContextMismatch ("marked variable list", x)))

/// <summary>
///     Pretty printers for <c>Sub</c>.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty


    /// <summary>
    ///     Pretty-prints a <see cref="TraversalContext"/>.
    /// </summary>
    let printTraversalContext : TraversalContext -> Doc =
        // TODO(CaptainHayashi): proper doc comment.
        let printPosition =
            function
            | Positive -> String "+"
            | Negative -> String "-"

        function
        | NoCtx -> String "(no context)"
        | Positions [] -> String "(empty position stack)"
        | Positions xs -> colonSep [ String "position stack"
                                     hjoin (List.map printPosition xs) ]
        | Vars xs -> colonSep [ String "variables"
                                commaSep (List.map printTypedVar xs) ]
        | MarkedVars xs -> colonSep [ String "marked variables"
                                      commaSep (List.map (printCTyped printMarkedVar) xs) ]

    /// <summary>
    ///     Pretty-prints a <see cref="TraversalError"/>.
    /// </summary>
    /// <param name="pInner">Pretty-printer for wrapped errors.</param>
    /// <typeparam name="Inner">Type for wrapped errors.</typeparam>
    /// <returns>
    ///     A function pretty-printing <see cref="TraversalError"/>s.
    /// </returns>
    let printTraversalError (pInner : 'Inner -> Doc) : TraversalError<'Inner> -> Doc =
        function
        | Inner e -> pInner e
        | BadType (expected, got) ->
            fmt "Type mismatch after substitution: expected {0}, got {1}"
                [ printType expected; printType got ]
        | ContextMismatch (expected, got) ->
            fmt "Internal context mismatch: expected {0}, got {1}"
                [ String expected; printTraversalContext got ]
