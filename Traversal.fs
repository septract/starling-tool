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
    /// <typeparam name="Var">The type of variables in finding contexts.</param>
    type TraversalContext<'Var> =
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
        /// <summary>A context for searching for variables.</summary>
        | Vars of CTyped<'Var> list
        /// <summary>
        ///     A context for checking whether we've entered an array index.
        /// </summary>
        | InIndex of bool
        override this.ToString () = sprintf "%A" this


    /// <summary>
    ///     Removes the variables from a variable context.
    /// </summary>
    let stripVars (ctx : TraversalContext<_>) : TraversalContext<unit> =
        match ctx with
        | Vars _ -> Vars []
        | Positions pl -> Positions pl
        | InIndex b -> InIndex b
        | NoCtx -> NoCtx

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
    /// <param name="ctx">The context to change.</param>
    /// <typeparam name="Var">The type of variables in finding contexts.</param>
    /// <returns>
    ///     If the context is not
    ///     <c>Positions</c>, it does not change the <c>TraversalContext</c>; else,
    ///     it pushes a new position that is <c>f c</c>, where <c>c</c> is
    ///     the current position.
    /// </returns>
    let push
      (f : Position -> Position)
      (ctx : TraversalContext<'Var>)
      : TraversalContext<'Var> =
        match ctx with
        | Positions [] -> failwith "empty position stack"
        | Positions (x::xs) -> Positions ((f x)::x::xs)
        | x -> x

    /// <summary>
    ///     Sets IsIndex to true for the duration of a traversal.
    /// </summary>
    /// <param name="trav">The traversal to modify.</param>
    /// <param name="ctx">The current context.</param>
    /// <typeparam name="Src">
    ///     The input type of <paramref name="trav"/>, less the context.
    /// </typeparam>
    /// <typeparam name="Dst">
    ///     The return type of <paramref name="trav"/>, less the context.
    /// </typeparam>
    /// <typeparam name="Var">The type of variables in finding contexts.</param>
    /// <returns>
    ///     A function over a <c>TraversalContext</c>, which behaves as
    ///     <paramref name="trav"/>, but, if the <c>TraversalContext</c> is
    ///     <c>InIndex</c>, has this set to true for the duration of the
    ///     traversal.
    /// </returns>
    let inIndex
      (g : TraversalContext<'Var> -> 'Src -> Result<TraversalContext<'Var> * 'Dst, 'Error>)
      (ctx : TraversalContext<'Var>)
      : 'Src -> Result<TraversalContext<'Var> * 'Dst, 'Error> =
        let ctx' =
            match ctx with
            | InIndex _ -> InIndex true
            | x -> x

        let travResult = g ctx'
        let resetCtx ctx'' =
            match ctx'' with
            | InIndex _ -> ctx
            | x -> x

        g ctx' >> lift (pairMap resetCtx id)

    /// <summary>
    ///     If the context is position-based, pop the position stack.
    /// </summary>
    /// <param name="ctx">The current context.</param>
    /// <typeparam name="Var">The type of variables in finding contexts.</param>
    /// <returns>
    ///     A function over a <c>TraversalContext</c>.  If the context is not
    ///     <c>Positions</c>, it does not change the <c>TraversalContext</c>; else,
    ///     it pops the current position.
    /// </returns>
    let pop (ctx : TraversalContext<'Var>) : TraversalContext<'Var> =
        match ctx with
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
    /// <param name="ctx">The current context.</param>
    /// <typeparam name="Var">The type of variables in finding contexts.</param>
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
      (g : TraversalContext<'Var> -> 'Src -> Result<TraversalContext<'Var> * 'Dst, 'Error>)
      (ctx : TraversalContext<'Var>)
      : 'Src -> Result<TraversalContext<'Var> * 'Dst, 'Error> =
        g (push f ctx) >> lift (pairMap pop id)

    /// <summary>
    ///     An initial positive position context.
    /// </summary>
    let positive () : TraversalContext<unit> = Positions [Positive]

    /// <summary>
    ///     An initial negative position context.
    /// </summary>
    let negative () : TraversalContext<unit> = Positions [Negative]


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
    | ContextMismatch of expectedType : string * got : TraversalContext<unit>


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
/// <typeparam name="Var">
///     The type of variables collected in the traversal.
/// </typeparam>
type Traversal<'Src, 'Dst, 'Error, 'Var> =
    TraversalContext<'Var> -> 'Src ->
        Result<TraversalContext<'Var> * 'Dst, TraversalError<'Error>>

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
/// <typeparam name="Var">
///     The type of variables collected in the traversal.
/// </typeparam>
/// <returns>
///     The traversal <paramref name="f"/> lifted such that it accepts
///     <see cref="NoCtx"/> (and then discards it).
/// </returns>
let mapTraversal
  (f : Traversal<'Src, 'Dst, 'Error, 'Var>) : 'Src -> Result<'Dst, TraversalError<'Error>> =
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
/// <typeparam name="Var">
///     The type of variables collected in the traversal.
/// </typeparam>
/// <returns>
///     The function <paramref name="f"/> lifted such that it can be used
///     in a traversal.
/// </returns>
let ignoreContext
  (f : 'Src -> Result<'Dst, TraversalError<'Error>>) : Traversal<'Src, 'Dst, 'Error, 'Var> =
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
  (lift : Traversal<'SrcA, 'DstA, 'ErrorA, unit> -> Traversal<'SrcB, 'DstB, 'ErrorB, unit>)
  : 'SrcB -> Result<'DstB, TraversalError<'ErrorB>> =
    mapTraversal (lift (ignoreContext (f >> mapMessages Inner)))

/// <summary>
///     Lifts a traversal over <see cref="CTyped"/>.
/// </summary>
let tliftOverCTyped
  (sub : Traversal<'Src, 'Dest, 'Error, 'Var>)
  : Traversal<CTyped<'Src>, CTyped<'Dest>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        function
        | CTyped.Int   (t, i) -> lift (fun (ctx, i') -> (ctx, Int   (t, i'))) (sub ctx i)
        | CTyped.Bool  (t, b) -> lift (fun (ctx, b') -> (ctx, Bool  (t, b'))) (sub ctx b)
        | CTyped.Array (t, a) -> lift (fun (ctx, a') -> (ctx, Array (t, a'))) (sub ctx a)

/// <summary>
///     Tries to extract an <see cref="ArrayExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type
///     or the element type or array is wrong.
/// </summary>
/// <param name="typerec">The expected type record of the expression.</param>
/// <param name="expr">The expression from which we are extracting.</param>
/// <returns>
///     On success, the array expression nested inside <paramref name="expr"/>.
///     On failure, a <see cref="TraversalError"/> explaining why.
/// </returns>
let expectArray (typerec : ArrayTypeRec) (expr : Expr<'Var>)
  : Result<ArrayExpr<'Var>, TraversalError<_>> =
    match expr with
    | Expr.Array (t, x) when arrayTypeRecsCompatible typerec t -> ok x
    | e -> fail (BadType (expected = Type.Array (typerec, ()), got = typeOf e))

/// <summary>
///     Tries to extract an <see cref="IntExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type.
/// </summary>
/// <param name="typerec">The expected type record of the expression.</param>
/// <param name="expr">The expression from which we are extracting.</param>
/// <returns>
///     On success, the array expression nested inside <paramref name="expr"/>.
///     On failure, a <see cref="TraversalError"/> explaining why.
/// </returns>
let expectInt (typerec : PrimTypeRec) (expr : Expr<'Var>)
  : Result<IntExpr<'Var>, TraversalError<_>> =
    match expr with
    | Expr.Int (t, x) when primTypeRecsCompatible typerec t -> ok x
    | e -> fail (BadType (expected = Type.Int (typerec, ()), got = typeOf e))

/// <summary>
///     Tries to extract an <see cref="BoolExpr"/> out of an
///     <see cref="Expr"/>, failing if the expression is not of that type.
/// </summary>
/// <param name="typerec">The expected type record of the expression.</param>
/// <param name="expr">The expression from which we are extracting.</param>
/// <returns>
///     On success, the array expression nested inside <paramref name="expr"/>.
///     On failure, a <see cref="TraversalError"/> explaining why.
/// </returns>
let expectBool (typerec : PrimTypeRec) (expr : Expr<'Var>) 
  : Result<BoolExpr<'Var>, TraversalError<_>> =
    match expr with
    | Expr.Bool (t, x) when primTypeRecsCompatible typerec t -> ok x
    | e -> fail (BadType (expected = Type.Bool (typerec, ()), got = typeOf e))

/// <summary>
///     Maps a traversal over an item, feeds the result into a function,
///     and returns the final context and the result of that function.
/// </summary>
let tchain (f : Traversal<'A, 'AR, 'Error, 'Var>) (g : 'AR -> 'Result)
  : Traversal<'A, 'Result, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx -> f ctx >> lift (fun (ctxF, xR) -> ctxF, g xR)

/// <summary>
///     Maps a traversal from left to right over a list, accumulating the
///     context, feeds the result list into a function, and returns the
///     final context and the result of that function.
/// </summary>
let tchainL (f : Traversal<'A, 'AR, 'Error, 'Var>) (g : 'AR list -> 'Result)
  : Traversal<'A list, 'Result, 'Error, 'Var> =
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
let tchainM (f : Traversal<'A, 'AR, 'Error, 'Var>) (g : Multiset<'AR> -> 'Result)
  : Traversal<Multiset<'A>, 'Result, 'Error, 'Var> =
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
  (f : Traversal<'A, 'AR, 'Error, 'Var>)
  (g : Traversal<'B, 'BR, 'Error, 'Var>)
  (h : ('AR * 'BR) -> 'Result)
  : Traversal<'A * 'B, 'Result, 'Error, 'Var> =
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
  (f : Traversal<'A, 'AR, 'Error, 'Var>)
  (g : Traversal<'B, 'BR, 'Error, 'Var>)
  (h : Traversal<'C, 'CR, 'Error, 'Var>)
  (i : ('AR * 'BR * 'CR) -> 'Result)
  : Traversal<'A * 'B * 'C, 'Result, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx (x, y, z) ->
        trial {
            let! ctxF, xR = f ctx x
            let! ctxG, yR = g ctxF y
            let! ctxH, zR = h ctxG z
            return (ctxH, i (xR, yR, zR))
        }

/// <summary>
///     Re-annotates a pair of expressions with types before feeding them to a
///     constructor.
/// </summary>
let retype2 x y f (x', y') =
    f (updateTypedSub x x', updateTypedSub y y')

/// <summary>
///     Converts a traversal from typed variables to expressions to one from
///     Boolean expressions to Boolean expressions.
/// </summary>
let rec tliftToBoolSrc
    (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
    : Traversal<TypedBoolExpr<'SrcVar>, BoolExpr<'DstVar>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.

    // We do some tricky inserting and removing of positions on the stack
    // to ensure the correct position appears in the correct place, and
    // is removed when we pop back up the expression stack.
    let isv x = Context.changePos id (tliftToIntSrc sub) x
    let esv x = Context.changePos id (tliftToExprSrc sub) x
    let asv x = Context.changePos id (tliftToArraySrc sub) x

    let neg = Context.negate

    fun ctx b ->
        let bsv f ctx x = Context.changePos f (tliftToBoolSrc sub) ctx (updateTypedSub b x)

        match stripTypeRec b with
        | BVar x ->
            bind (uncurry (ignoreContext (expectBool b.SRec)))
                (Context.changePos id sub ctx (CTyped.Bool (b.SRec, x)))
        | BIdx (arr, ix) ->
            let tResult =
                tchain2 asv
                    (Context.inIndex isv)
                    (fun (a, i) -> ok (BIdx (updateTypedSub arr a, i)))
                    ctx
                    (arr, mkTypedSub normalRec ix)
            // Remove the nested result.
            bind (uncurry (ignoreContext id)) tResult
        | BTrue -> ok (ctx, BTrue)
        | BFalse -> ok (ctx, BFalse)
        | BAnd xs -> tchainL (bsv id) BAnd ctx xs
        | BOr xs  -> tchainL (bsv id) BOr ctx xs
        // The LHS of an implies is in negative position.
        | BImplies (x, y) -> tchain2 (bsv neg) (bsv id) BImplies ctx (x, y)
        | BEq (x, y) -> tchain2 esv esv BEq ctx (x, y)
        // These are complex because they encode the type of their integer arguments.
        | BGt (x, y) -> tchain2 isv isv (retype2 x y BGt) ctx (x, y)
        | BGe (x, y) -> tchain2 isv isv (retype2 x y BGe) ctx (x, y)
        | BLe (x, y) -> tchain2 isv isv (retype2 x y BLe) ctx (x, y)
        | BLt (x, y) -> tchain2 isv isv (retype2 x y BLt) ctx (x, y)
        | BNot x -> tchain (bsv neg) BNot ctx x

/// <summary>
///     Converts a traversal from typed variables to expressions to one from
///     integral expressions to integral expressions.
/// </summary>
and tliftToIntSrc
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
  : Traversal<TypedIntExpr<'SrcVar>, IntExpr<'DstVar>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    let asv ctx = Context.changePos id (tliftToArraySrc sub) ctx
    // Integral traversal with a different type from this expression
    let tisv ctx = Context.changePos id (tliftToIntSrc sub) ctx

    fun ctx i ->
        // Integral traversal with the same type as this expression
        let isv ctx x = Context.changePos id (tliftToIntSrc sub) ctx (updateTypedSub i x)

        match stripTypeRec i with
        | IVar x ->
            bind (uncurry (ignoreContext (expectInt i.SRec)))
                (Context.changePos id sub ctx (CTyped.Int (i.SRec, x)))
        | IIdx (arr, ix) ->
            let tResult =
                tchain2
                    asv
                    (Context.inIndex tisv)
                    (fun (a, i) -> ok (IIdx (updateTypedSub arr a, i)))
                    ctx
                    (arr, mkTypedSub normalRec ix)
            // Remove the nested result.
            bind (uncurry (ignoreContext id)) tResult
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
and tliftToArraySrc
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
  : Traversal<TypedArrayExpr<'SrcVar>, ArrayExpr<'DstVar>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    let isv x = Context.changePos id (tliftToIntSrc sub) x
    let esv x = Context.changePos id (tliftToExprSrc sub) x
    // Array traversal with a different type from this expression
    let tasv ctx = Context.changePos id (tliftToArraySrc sub) ctx

    fun ctx a ->
        // Array traversal with the same type as this expression
        let asv ctx x = Context.changePos id (tliftToArraySrc sub) ctx (updateTypedSub a x)

        match stripTypeRec a with
        | AVar x ->
            bind (uncurry (ignoreContext (expectArray a.SRec)))
                (Context.changePos id sub ctx (CTyped.Array (a.SRec, x)))
        | AIdx (arr, ix) ->
            let tResult =
                tchain2
                    tasv
                    (Context.inIndex isv)
                    (fun (a, i) -> ok (AIdx (updateTypedSub arr a, i)))
                    ctx
                    (arr, mkTypedSub normalRec ix)
            // Remove the nested result.
            bind (uncurry (ignoreContext id)) tResult
        | AUpd (arr, ix, value) ->
            let assemble (arr', ix', value') =
                // Ensure the traversal doesn't change the type of value.
                let vt, vt' = typeOf value, typeOf value'
                if typesCompatible vt vt'
                then ok (AUpd (arr', ix', value'))
                else fail (BadType (expected = vt, got = vt'))
            let tResult =
                tchain3
                    asv
                    (Context.inIndex isv)
                    esv
                    assemble ctx (arr, mkTypedSub normalRec ix, value)

            // Remove the nested result.
            bind (uncurry (ignoreContext id)) tResult

and tliftToExprSrc
  (sub : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
  : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx ->
        function
        | Bool (t, b) ->
            let tb = mkTypedSub t b
            let tR = tliftToBoolSrc sub ctx tb
            lift (fun (ctx, b') -> (ctx, Bool (t, b'))) tR
        | Int (t, i) ->
            let ti = mkTypedSub t i
            let tR = tliftToIntSrc sub ctx ti
            lift (fun (ctx, i') -> (ctx, Int (t, i'))) tR
        | Array (t, a) ->
            let ta = mkTypedSub t a
            let tR = tliftToArraySrc sub ctx ta
            lift (fun (ctx, a') -> (ctx, Array (t, a'))) tR

/// <summary>
///     Adapts an expression traversal to work on Boolean expressions.
///     Fails if the traversal responds with a non-Boolean expression.
/// </summary>
let traverseBoolAsExpr
  (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
  : Traversal<TypedBoolExpr<'SrcVar>, BoolExpr<'DstVar>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx bool ->
        let expr = Expr.Bool (bool.SRec, bool.SExpr)
        let R = traversal ctx expr
        bind (uncurry (ignoreContext (expectBool bool.SRec))) R

/// <summary>
///     Adapts an expression traversal to work on integer expressions.
///     Fails if the traversal responds with a non-integer expression.
/// </summary>
let traverseIntAsExpr
  (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
  : Traversal<TypedIntExpr<'SrcVar>, IntExpr<'DstVar>, 'Error, 'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx int ->
        let expr = Expr.Int (int.SRec, int.SExpr)
        let R = traversal ctx expr
        bind (uncurry (ignoreContext (expectInt int.SRec))) R

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
  (sub : Traversal<CTyped<'SrcVar>, CTyped<'DstVar>, 'Error, 'Var>)
  : Traversal<CTyped<'SrcVar>, Expr<'DstVar>, 'Error, 'Var> =
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
  (sub : Traversal<CTyped<'SrcVar>, CTyped<'DstVar>, 'Error, 'Var>)
  : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var> =
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
let pushVar (ctx : TraversalContext<'Var>) (v : CTyped<'Var>)
  : Result<TraversalContext<'Var>, TraversalError<'Error>>=
    // TODO(CaptainHayashi): proper doc comment.
    match ctx with
    | Vars vs -> ok (Vars (v::vs))
    | c -> fail (ContextMismatch ("vars context", stripVars c))

/// <summary>
///     Traversal for accumulating variables.
/// <summary>
let collectVars : Traversal<CTyped<'Var>, CTyped<'Var>, 'Error, 'Var>  =
    // TODO(CaptainHayashi): proper doc comment.
    fun ctx v -> lift (fun ctx -> (ctx, v)) (pushVar ctx v)

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
  (t : Traversal<'Subject, _, 'Error, 'Var>)
  (subject : 'Subject)
  : Result<Set<CTyped<'Var>>, TraversalError<'Error>> =
    subject
    |> t (Vars [])
    |> bind
        (function
         | (Vars xs, _) -> ok (Set.ofList xs)
         | (x, _) -> fail (ContextMismatch ("variable list", stripVars x)))

///     Pretty printers for <c>Sub</c>.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty


    /// <summary>
    ///     Pretty-prints a <see cref="TraversalContext"/>.
    /// </summary>
    let printTraversalContext (ctx: TraversalContext<unit>) : Doc =
        // TODO(CaptainHayashi): proper doc comment.
        let printPosition =
            function
            | Positive -> String "+"
            | Negative -> String "-"

        match ctx with
        | NoCtx -> String "(no context)"
        | InIndex true -> String "in index"
        | InIndex false -> String "not in index"
        | Positions [] -> String "(empty position stack)"
        | Positions xs -> colonSep [ String "position stack"
                                     hjoin (List.map printPosition xs) ]
        | Vars xs -> String "(variables)"

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
