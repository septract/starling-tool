/// Functions for substituting expressions.
module Starling.Sub

open Starling.Collections
open Starling.Expr
open Starling.Model

(*
 * Basic substitution system
 *)

/// Type for substitution function tables.
[<NoComparison>]
[<NoEquality>]
type SubFun =
    {ASub: ArithExpr -> ArithExpr
     BSub: BoolExpr -> BoolExpr}

/// <summary>
///   Runs the given <c>SubFun</c> on an <c>Expr</c>.
/// </summary>
let subExpr { ASub = fa; BSub = fb } =
    function
    | AExpr a -> a |> fa |> AExpr
    | BExpr b -> b |> fb |> BExpr


(*
 * Model element substitution functions
 *)

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>VFunc</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>VFunc</c>.
/// </param>
/// <param name="func">
///   The <c>VFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>VFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>VFunc</c> are its parameters.
///   </para>
/// </remarks>
let subExprInVFunc sub func =
    { func with Params = List.map (subExpr sub) func.Params }

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>GFunc</c>.
/// </summary>
/// <param name="_arg1">
///   The <c>GFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>GFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>GFunc</c> are the guard itself, and
///     the expressions of the enclosed <c>VFunc</c>.
///   </para>
/// </remarks
let subExprInGFunc sub {Cond = cond; Item = item} =
    { Cond = sub.BSub cond
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
/// <returns>
///   The <c>GView</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>GView</c> are those of its constituent
///     <c>GFunc</c>s.
///   </para>
/// </remarks>
let subExprInGView sub = Multiset.map (subExprInGFunc sub)

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>DTerm</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>DTerm</c>.
/// </param>
/// <param name="_arg1">
///   The <c>DTerm</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>DTerm</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>DTerm</c> are those of its constituent
///     command (<c>BoolExpr</c>), its weakest precondition
///     (<c>GView</c>), and its goal (<c>VFunc</c>).
///   </para>
/// </remarks>
let subExprInDTerm sub =
    mapTerm (sub.BSub) (subExprInGView sub) (subExprInVFunc sub)


(*
 * Variable substitution (special case of substitution)
 *)

/// Type for variable substitution function tables.
[<NoComparison>]
[<NoEquality>]
type VSubFun =
    {AVSub: Const -> ArithExpr
     BVSub: Const -> BoolExpr}

/// Substitutes all variables with the given substitution function set
/// for the given Boolean expression.
let rec boolSubVars vfun =
    function 
    | BConst x -> vfun.BVSub x
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
and arithSubVars vfun =
    function 
    | AConst x -> vfun.AVSub x
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
    { ASub = arithSubVars vsub
      BSub = boolSubVars vsub }


(*
 * Variable marking (special case of variable substitution)
 *)

/// Lifts a variable set to a marking predicate.
let inSet st var = Set.contains var st

/// Lifts a marking function to a variable substitution function table.
let liftMarkerV marker vpred =
    let gfun = function | Unmarked s when vpred s -> marker s
                        | x -> x
    {AVSub = gfun >> AConst
     BVSub = gfun >> BConst}

/// Lifts a marking function to a substitution function table.
let liftMarker marker vpred =
    onVars (liftMarkerV marker vpred)
