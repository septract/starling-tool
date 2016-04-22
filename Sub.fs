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
open Starling.Core.Model
open Starling.Core.GuardedView


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
 * Basic substitution system
 *)

/// <summary>
///   Runs the given <c>SubFun</c> on an <c>Expr</c>.
/// </summary>
let subExpr : SubFun<'srcVar, 'dstVar> -> Expr<'srcVar> -> Expr<'dstVar> =
    Mapper.map

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
    { Cond = Mapper.mapBool sub cond
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
        (Mapper.mapBool sub)
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
    |> List.map (Mapper.tryMap sub)
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
        (Mapper.mapBool sub cond)
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
        (Mapper.mapBool sub)
        (trySubExprInGView sub)
        (trySubExprInVFunc sub)


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
    | BEq (x, y) -> BEq (subExpr (onVars vfun) x,
                         subExpr (onVars vfun) y)
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

/// Lifts a variable set to a marking predicate.
let inSet st var = Set.contains var st

/// Lifts a VSubFun over MarkedVars to deal with symbolic vars.
let rec liftVToSym
  (sf : VSubFun<'srcVar, Sym<'dstVar>>)
  : VSubFun<Sym<'srcVar>, Sym<'dstVar>> =
    Mapper.make
        (function
         | Reg r -> Mapper.mapInt sf r
         | Sym { Name = sym; Params = rs } ->
             // TODO(CaptainHayashi): this is horrible.
             // Are our abstractions wrong?
           AVar <| Sym
               { Name = sym
                 Params = List.map (sf
                                    |> liftVToSym
                                    |> onVars
                                    |> Mapper.map) rs } )
        (function
         | Reg r -> Mapper.mapBool sf r
         | Sym { Name = sym; Params = rs } ->
           BVar <| Sym
               { Name = sym
                 Params = List.map (sf
                                    |> liftVToSym
                                    |> onVars
                                    |> Mapper.map) rs } )


/// Lifts a marking function to a variable substitution function table.
let liftMarkerV marker vpred =
    (function
     | Unmarked s when vpred s -> Reg (marker s)
     | x -> Reg x)
    |> Mapper.cmake
    |> liftVSubFun
    |> liftVToSym

/// Lifts a marking function to a substitution function table.
let liftMarker marker vpred =
    onVars (liftMarkerV marker vpred)


(*
 * Common substitutions
 *)

/// Converts an expression to its pre-state.
let before
  : SubFun<Sym<Var>, Sym<MarkedVar>> =
    (Before >> Reg)
    |> Mapper.cmake
    |> liftVSubFun
    |> liftVToSym
    |> onVars

/// Converts an expression to its post-state.
let after
  : SubFun<Sym<Var>, Sym<MarkedVar>> =
    (After >> Reg)
    |> Mapper.cmake
    |> liftVSubFun
    |> liftVToSym
    |> onVars

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
///     Substitution table for removing symbols from expressions.
/// </summary>
/// <param name="err">
///     Function mapping a symbol's contents to an error to throw when
///     detecting one.
/// </param>
/// <typeparam name="err">
///     The type of <paramref name="err"/>.
/// </typeparam>
/// <typeparam name="err">
///     The type of regular (non-symbolic) variables.
/// </typeparam>
/// <returns>
///     A <c>TrySubFun</c> trying to remove symbols.
/// </returns>
let tsfRemoveSym
  (err : string -> 'err)
  : TrySubFun<Sym<'var>, 'var, 'err> =
    tryOnVars <| Mapper.make
        (function
         | Sym s -> s.Name |> err |> fail
         | Reg f -> f |> AVar |> ok)
        (function
         | Sym s -> s.Name |> err |> fail
         | Reg f -> f |> BVar |> ok)
