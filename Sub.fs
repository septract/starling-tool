/// <summary>
///     Functions for substituting expressions.
/// </summary>
module Starling.Core.Sub

open Chessie.ErrorHandling

open Starling.Utils
open Starling.Collections

open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.GuardedView


/// <summary>
///     Types used in expression substitution.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A <c>TypeMap</c> mapping between forms of <c>Expr</c>s.
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
        TypeMapper<
            IntExpr<'srcVar>, BoolExpr<'srcVar>,
            IntExpr<'dstVar>, BoolExpr<'dstVar>>

    /// <summary>
    ///     A possibly failing <c>TypeMap</c> mapping between forms of <c>Expr</c>s.
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
        TypeMapper<
            IntExpr<'srcVar>, BoolExpr<'srcVar>,
            Result<IntExpr<'dstVar>, 'err>,
            Result<BoolExpr<'dstVar>, 'err>>

    /// <summary>
    ///     A <c>TypeMap</c> mapping between forms of <c>Var</c>s.
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
        TypeMapper<'srcVar, 'srcVar, IntExpr<'dstVar>, BoolExpr<'dstVar>>


(*
 * Basic substitution system
 *)

/// <summary>
///   Runs the given <c>SubFun</c> on an <c>Expr</c>.
/// </summary>
let subExpr : SubFun<'srcVar, 'dstVar> -> Expr<'srcVar> -> Expr<'dstVar> =
    TypeMapper.map

(*
 * Model element substitution functions
 *)

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>VFunc</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>VFunc</c>.
/// </param>
/// <param name="_arg1">
///   The <c>VFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <returns>
///   The <c>VFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>VFunc</c> are its parameters.
///   </para>
/// </remarks>
let subExprInVFunc
  (sub : SubFun<'srcVar, 'dstVar>)
  ( { Name = n ; Params = ps } : VFunc<'srcVar> )
  : VFunc<'dstVar> =
    { Name = n ; Params = List.map (subExpr sub) ps }

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>GFunc</c>.
/// </summary>
/// <param name="_arg1">
///   The <c>GFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <returns>
///   The <c>GFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>GFunc</c> are the guard itself, and
///     the expressions of the enclosed <c>VFunc</c>.
///   </para>
/// </remarks>
let subExprInGFunc
  (sub : SubFun<'srcVar, 'dstVar>)
  ( { Cond = cond ; Item = item } : GFunc<'srcVar> )
  : GFunc<'dstVar> =
    { Cond = TypeMapper.mapBool sub cond
      Item = subExprInVFunc sub item }

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>GView</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>GView</c>.
/// </param>
/// <param name="_arg1">
///   The <c>GView</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <returns>
///   The <c>GView</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>GView</c> are those of its constituent
///     <c>GFunc</c>s.
///   </para>
/// </remarks>
let subExprInGView
  (sub : SubFun<'srcVar, 'dstVar>)
  : GView<'srcVar>
  -> GView<'dstVar> =
    Multiset.map (subExprInGFunc sub)

/// <summary>
///     Maps a <c>SubFun</c> over all expressions in an <c>Term</c>
///     over a <c>GView</c> weakest-pre and <c>VFunc</c> goal.
/// </summary>
/// <param name="sub">
///     The <c>SubFun</c> to map over all expressions in the <c>STerm</c>.
/// </param>
/// <param name="term">
///     The <c>Term</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <returns>
///     The <c>Term</c> resulting from the mapping.
/// </returns>
/// <remarks>
///     <para>
///         The expressions in the term are those of its
///         constituent command (<c>BoolExpr</c>), its weakest
///         precondition (<c>GView</c>), and its goal (<c>VFunc</c>).
///     </para>
/// </remarks>
let subExprInDTerm
  (sub : SubFun<'srcVar, 'dstVar>)
  (term : Term<BoolExpr<'srcVar>, GView<'srcVar>, VFunc<'srcVar>>)
  : Term<BoolExpr<'dstVar>, GView<'dstVar>, VFunc<'dstVar>> =
    mapTerm
        (TypeMapper.mapBool sub)
        (subExprInGView sub)
        (subExprInVFunc sub)
        term

/// <summary>
///     Maps a <c>TrySubFun</c> over all expressions in a <c>VFunc</c>.
/// </summary>
/// <param name="sub">
///     The <c>TrySubFun</c> to map over all expressions in the <c>VFunc</c>.
/// </param>
/// <param name="_arg1">
///     The <c>VFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <typeparam name="err">
///     The type of any returned errors.
/// </typeparam>
/// <returns>
///     The Chessie-wrapped <c>VFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///     <para>
///         The expressions in a <c>VFunc</c> are its parameters.
///     </para>
/// </remarks>
let trySubExprInVFunc
  (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
  ( { Name = n ; Params = ps } : VFunc<'srcVar> )
  : Result<VFunc<'dstVar>, 'err> =
    ps
    |> List.map (TypeMapper.tryMap sub)
    |> collect
    |> lift (fun ps' -> { Name = n ; Params = ps' } )

/// <summary>
///     Maps a <c>TrySubFun</c> over all expressions in a <c>GFunc</c>.
/// </summary>
/// <param name="_arg1">
///     The <c>GFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <typeparam name="err">
///     The type of errors occurring in the map.
/// </typeparam>
/// <returns>
///     The Chessie-wrapped <c>GFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///     <para>
///         The expressions in a <c>GFunc</c> are the guard itself, and
///         the expressions of the enclosed <c>VFunc</c>.
///     </para>
/// </remarks>
let trySubExprInGFunc
  (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
  ( { Cond = cond ; Item = item } : GFunc<'srcVar> )
  : Result<GFunc<'dstVar>, 'err> =
    lift2
        (fun cond' item' -> { Cond = cond' ; Item = item' } )
        (TypeMapper.mapBool sub cond)
        (trySubExprInVFunc sub item)

/// <summary>
///     Maps a <c>TrySubFun</c> over all expressions in a <c>GView</c>.
/// </summary>
/// <param name="sub">
///     The <c>TrySubFun</c> to map over all expressions in the
///     <c>GView</c>.
/// </param>
/// <param name="_arg1">
///     The <c>GView</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <typeparam name="err">
///     The type of any returned errors.
/// </typeparam>
/// <returns>
///     The Chessie-wrapped <c>GView</c> resulting from the mapping.
/// </returns>
/// <remarks>
///     <para>
///         The expressions in a <c>GView</c> are those of its
///         constituent <c>GFunc</c>s.
///     </para>
/// </remarks>
let trySubExprInGView
  (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
  : GView<'srcVar> -> Result<GView<'dstVar>, 'err> =
    Multiset.toFlatList
    >> List.map (trySubExprInGFunc sub)
    >> collect
    >> lift Multiset.ofFlatList

/// <summary>
///     Maps a <c>TrySubFun</c> over all expressions in a <c>Term</c>
///     over a <c>GView</c> weakest-pre and <c>VFunc</c> goal.
/// </summary>
/// <param name="sub">
///     The <c>TrySubFun</c> to map over all expressions in the
///     <c>Term</c>.
/// </param>
/// <param name="_arg1">
///     The <c>Term</c> over which whose expressions are to be mapped.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables entering the map.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables leaving the map.
/// </typeparam>
/// <typeparam name="err">
///     The type of any returned errors.
/// </typeparam>
/// <returns>
///     The Chessie-wrapped <c>Term</c> resulting from the mapping.
/// </returns>
/// <remarks>
///     <para>
///         The expressions in the term are those of its
///         constituent command (<c>BoolExpr</c>), its weakest
///         precondition (<c>GView</c>), and its goal (<c>VFunc</c>).
///     </para>
/// </remarks>
let trySubExprInDTerm
  (sub : TrySubFun<'srcVar, 'dstVar, 'err>)
  : Term<BoolExpr<'srcVar>, GView<'srcVar>, VFunc<'srcVar>>
  -> Result<Term<BoolExpr<'dstVar>, GView<'dstVar>, VFunc<'dstVar>>, 'err> =
    tryMapTerm
        (TypeMapper.mapBool sub)
        (trySubExprInGView sub)
        (trySubExprInVFunc sub)


(*
 * Variable substitution (special case of substitution)
 *)

/// Substitutes all variables with the given substitution function set
/// for the given Boolean expression.
let rec boolSubVars (vfun : VSubFun<'srcVar, 'dstVar>) =
    function 
    | BVar x -> TypeMapper.mapBool vfun x
    | BTrue -> BTrue
    | BFalse -> BFalse
    | BAnd xs -> BAnd (List.map (boolSubVars vfun) xs)
    | BOr xs -> BOr (List.map (boolSubVars vfun) xs)
    | BImplies (x, y) -> BImplies (boolSubVars vfun x,
                                   boolSubVars vfun y)
    | BEq (x, y) -> BEq (subExpr (onVars vfun) x,
                         subExpr (onVars vfun) y)
    | BGt (x, y) -> BGt (arithSubVars vfun x,
                         arithSubVars vfun y)
    | BGe (x, y) -> BGe (arithSubVars vfun x,
                         arithSubVars vfun y)
    | BLe (x, y) -> BLe (arithSubVars vfun x,
                         arithSubVars vfun y)
    | BLt (x, y) -> BLt (arithSubVars vfun x,
                         arithSubVars vfun y)
    | BNot x -> BNot (boolSubVars vfun x)

/// Substitutes all variables with the given substitution function
/// for the given arithmetic expression.
and arithSubVars (vfun : VSubFun<'srcVar, 'dstVar>) =
    function 
    | AVar x -> TypeMapper.mapInt vfun x
    | AInt i -> AInt i
    | AAdd xs -> AAdd (List.map (arithSubVars vfun) xs)
    | ASub xs -> ASub (List.map (arithSubVars vfun) xs)
    | AMul xs -> AMul (List.map (arithSubVars vfun) xs)
    | ADiv (x, y) -> ADiv (arithSubVars vfun x,
                           arithSubVars vfun y)

/// <summary>
///   Creates a <c>SubFun</c> from a <c>VSubFun</c>.
/// </summary>
and onVars vsub =
    TypeMapper.make (arithSubVars vsub) (boolSubVars vsub)


(*
 * Variable marking (special case of variable substitution)
 *)

/// Lifts a variable set to a marking predicate.
let inSet st var = Set.contains var st

/// Lifts a marking function to a variable substitution function table.
let liftMarkerV marker vpred =
    TypeMapper.compose
        (TypeMapper.cmake
             (function
              | Unmarked s when vpred s -> marker s
              | x -> x))
        (TypeMapper.make AVar BVar)

/// Lifts a marking function to a substitution function table.
let liftMarker marker vpred =
    onVars (liftMarkerV marker vpred)


(*
 * Common substitutions
 *)

/// Converts an expression to its pre-state.
let before = subExpr (liftMarker Before always)

/// Converts an expression to its post-state.
let after = subExpr (liftMarker After always)
