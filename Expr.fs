/// Utilities for working with expressions.
module Starling.Expr

open Starling.Utils
open Starling.Var

(*
 * Expression types
 *)

type Const =
    | Unmarked of string
    | Before of string
    | After of string
    | Frame of bigint * string

/// An expression of arbitrary type.
type Expr =
    | BExpr of BoolExpr
    | AExpr of ArithExpr

/// An arithmetic expression.
and ArithExpr =
    | AConst of Const
    | AInt of int64
    | AAdd of ArithExpr list
    | ASub of ArithExpr list
    | AMul of ArithExpr list
    | ADiv of ArithExpr * ArithExpr

/// A Boolean expression.
and BoolExpr =
    | BConst of Const
    | BTrue
    | BFalse
    | BAnd of BoolExpr list
    | BOr of BoolExpr list
    | BImplies of BoolExpr * BoolExpr
    | BEq of Expr * Expr
    | BGt of ArithExpr * ArithExpr
    | BGe of ArithExpr * ArithExpr
    | BLe of ArithExpr * ArithExpr
    | BLt of ArithExpr * ArithExpr
    | BNot of BoolExpr

/// Categorises arithmetic expressions into simple or compound.
let (|SimpleArith|CompoundArith|) =
    function
    | AConst _ | AInt _ -> SimpleArith
    | _ -> CompoundArith

/// Categorises Boolean expressions into simple or compound.
let (|SimpleBool|CompoundBool|) =
    function
    | BConst _ | BTrue | BFalse -> SimpleBool
    | _ -> CompoundBool

/// Categorises expressions into simple or compound.
let (|SimpleExpr|CompoundExpr|) =
    function
    | BExpr (SimpleBool) -> SimpleExpr
    | AExpr (SimpleArith) -> SimpleExpr
    | _ -> CompoundExpr

/// Returns true if the expression is definitely true.
/// This is sound, but not complete.
let isTrue =
    function | BTrue -> true
             | _ -> false

/// Returns true if the expression is definitely false.
/// This is sound, but not complete.
let isFalse =
    function | BFalse -> true
             | _ -> false

/// Converts a Starling constant into a string.
let constToString =
    function
    | Unmarked s -> s
    | Before s -> sprintf "%s!before" s
    | After s -> sprintf "%s!after" s
    | Frame (i, s) -> sprintf "%s!frame!%A" s i

(*
 * Expression constructors
 *)

/// Creates an unmarked arithmetic constant.
let aUnmarked c = c |> Unmarked |> AConst

/// Creates an after-marked arithmetic constant.
let aAfter c = c |> After |> AConst

/// Creates a before-marked arithmetic constant.
let aBefore c = c |> Before |> AConst

/// Creates an unmarked Boolean constant.
let bUnmarked c = c |> Unmarked |> BConst

/// Creates an after-marked Boolean constant.
let bAfter c = c |> After |> BConst

/// Creates a before-marked Boolean constant.
let bBefore c = c |> Before |> BConst


/// Creates a reference to a Boolean lvalue.
/// This does NOT check to see if the lvalue exists!
let mkBoolLV lv = 
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> Unmarked
    |> BConst

/// Creates a reference to an integer lvalue.
/// This does NOT check to see if the lvalue exists!
let mkIntLV lv = 
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> Unmarked
    |> AConst

/// Converts a type-name pair to an expression.
let mkVarExp (ty, name) =
    name
    |> Unmarked
    |> match ty with
       | Int -> AConst >> AExpr
       | Bool -> BConst >> BExpr

(* The following are just curried versions of the usual constructors. *)

/// Curried wrapper over BGt.
let mkGt = curry BGt
/// Curried wrapper over BGe.
let mkGe = curry BGe
/// Curried wrapper over BLt.
let mkLt = curry BLt
/// Curried wrapper over BLe.
let mkLe = curry BLe

/// Curried wrapper over BEq.
let mkEq = curry BEq

/// Makes an arithmetic equality.
let aEq = curry (pairMap AExpr AExpr >> BEq)

/// Makes a Boolean equality.
let bEq = curry (pairMap BExpr BExpr >> BEq)

/// Curried wrapper over ADiv.
let mkDiv = curry ADiv

/// Slightly optimised version of ctx.MkAnd.
/// Returns true for the empty array, and x for the singleton set {x}.
let mkAnd conjuncts =
    if Seq.exists isFalse conjuncts
    then BFalse
    else
        conjuncts
        |> Seq.filter (isTrue >> not)  // True terms redundant in AND.
        |> List.ofSeq
        |> function | [] -> BTrue  // True is the zero of AND.
                    | [x] -> x
                    | xs -> BAnd xs

/// Slightly optimised version of ctx.MkOr.
/// Returns false for the empty set, and x for the singleton set {x}.
let mkOr disjuncts =
    if Seq.exists isTrue disjuncts
    then BTrue
    else
        disjuncts
        |> Seq.filter (isFalse >> not)  // False terms redundant in OR.
        |> List.ofSeq
        |> function | [] -> BFalse  // False is the zero of OR.
                    | [x] -> x
                    | xs -> BOr xs

/// Makes an And from a pair of two expressions.
let mkAnd2 l r = mkAnd [l ; r]

/// Makes an Or from a pair of two expressions.
let mkOr2 l r = mkOr [l ; r]

/// Symbolically inverts a Boolean expression.
let rec mkNot =
    // Simplify obviously false or true exprs to their negation.
    function | BTrue -> BFalse
             | BFalse -> BTrue
             | BNot x -> x
             | BGt (x, y) -> BLe (x, y)
             | BGe (x, y) -> BLt (x, y)
             | BLe (x, y) -> BGt (x, y)
             | BLt (x, y) -> BGe (x, y)
             | BAnd xs -> BOr (List.map mkNot xs)
             | BOr xs -> BAnd (List.map mkNot xs) 
             | x -> BNot x

/// Makes not-equals.
let mkNeq l r = mkEq l r |> mkNot

/// Makes an implication from a pair of two expressions.
let mkImplies l r =
    (* l => r <-> ¬l v r.
     * This implies (excuse the pun) that l false or r true will
     * make the expression a tautology;
     * similarly, l true yields r, and r false yields ¬l.
     *)
    match l, r with
    | (BFalse, _) | (_, BTrue) -> BTrue
    | (x, BFalse) -> mkNot x
    | (BTrue, x) -> x
    | _ -> BImplies (l, r)

/// Makes an Add out of a pair of two expressions.
let mkAdd2 l r = AAdd [ l; r ]
/// Makes a Sub out of a pair of two expressions.
let mkSub2 l r = ASub [ l; r ]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 l r = AMul [ l; r ]

(*
 * Substitutions
 *)

/// Type for substitution function tables.
[<NoComparison>]
[<NoEquality>]
type SubFun =
    {ASub: Const -> ArithExpr
     BSub: Const -> BoolExpr}

/// Substitutes all variables with the given substitution function set
/// for the given Boolean expression.
let rec boolSubVars vfun =
    function 
    | BConst x -> vfun.BSub x
    | BTrue -> BTrue
    | BFalse -> BFalse
    | BAnd xs -> BAnd (List.map (boolSubVars vfun) xs)
    | BOr xs -> BOr (List.map (boolSubVars vfun) xs)
    | BImplies (x, y) -> BImplies (boolSubVars vfun x,
                                   boolSubVars vfun y)
    | BEq (x, y) -> BEq (subVars vfun x,
                         subVars vfun y)
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
    | AConst x -> vfun.ASub x
    | AInt i -> AInt i
    | AAdd xs -> AAdd (List.map (arithSubVars vfun) xs)
    | ASub xs -> ASub (List.map (arithSubVars vfun) xs)
    | AMul xs -> AMul (List.map (arithSubVars vfun) xs)
    | ADiv (x, y) -> ADiv (arithSubVars vfun x,
                           arithSubVars vfun y)

/// Substitutes all variables with the given substitution function for the
/// given expression.
and subVars vfun =
    function
    | AExpr a -> arithSubVars vfun a |> AExpr
    | BExpr b -> boolSubVars vfun b |> BExpr

(*
 * Variable marking (special case of variable substitution)
 *)

/// Lifts a variable set to a marking predicate.
let inSet st var = Set.contains var st

/// Lifts a marking function to a substitution function table.
let liftMarker marker vpred =
    let gfun = function | Unmarked s when vpred s -> marker s
                        | x -> x
    {ASub = (gfun >> AConst)
     BSub = (gfun >> BConst)}

/// Marks all variables in the given environment with the given marking
/// functions / pre-states for the given arithmetic expression.
let arithMarkVars marker vpred =
    arithSubVars (liftMarker marker vpred)

/// Marks all variables in the given environment with the given marking
/// functions / pre-states for the given Boolean expression.
let boolMarkVars marker vpred =
    boolSubVars (liftMarker marker vpred)

/// Marks all variables in the given set with the given marking
/// functions / pre-states for the given arbitrary expression.
let markVars marker vpred =
    subVars (liftMarker marker vpred)

(*
 * Fresh variable generation
 *)

/// Type for fresh variable generators.
type FreshGen = bigint ref

/// Creates a new fresh generator.
let freshGen () = ref 0I

/// Takes a fresh number out of the generator.
/// This method is NOT thread-safe.
let getFresh fg =
    let result = !fg
    fg := !fg + 1I
    result

/// Given a fresh generator, yields a function promoting a string to a frame
/// variable.
let frame fg = fg |> getFresh |> curry Frame

(*
 * Expression probing
 *)

/// Returns a set of all variables used in an arithmetic expression.
let rec varsInArith =
    function
    | AConst c -> Set.singleton c
    | AInt _ -> Set.empty
    | AAdd xs -> xs |> Seq.map varsInArith |> Set.unionMany
    | ASub xs -> xs |> Seq.map varsInArith |> Set.unionMany
    | AMul xs -> xs |> Seq.map varsInArith |> Set.unionMany
    | ADiv (x, y) -> Set.union (varsInArith x) (varsInArith y)

/// Returns a set of all variables used in a Boolean expression.
and varsInBool =
    function
    | BConst c -> Set.singleton c
    | BTrue -> Set.empty
    | BFalse -> Set.empty
    | BAnd xs -> xs |> Seq.map varsInBool |> Set.unionMany
    | BOr xs -> xs |> Seq.map varsInBool |> Set.unionMany
    | BImplies (x, y) -> Set.union (varsInBool x) (varsInBool y)
    | BEq (x, y) -> Set.union (varsIn x) (varsIn y)
    | BGt (x, y) -> Set.union (varsInArith x) (varsInArith y)
    | BGe (x, y) -> Set.union (varsInArith x) (varsInArith y)
    | BLe (x, y) -> Set.union (varsInArith x) (varsInArith y)
    | BLt (x, y) -> Set.union (varsInArith x) (varsInArith y)
    | BNot x -> varsInBool x

/// Returns a set of all variables used in an expression.
and varsIn =
    function
    | AExpr a -> varsInArith a
    | BExpr b -> varsInBool b
