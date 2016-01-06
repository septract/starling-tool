/// Utilities for working with expressions.
module Starling.Expr

open Chessie.ErrorHandling
open Microsoft  // TODO(CaptainHayashi): temporary
open Starling.Var
open Starling.Model
open Starling.Utils

(*
 * Temporary Z3 work
 *)

/// Returns all of the exprs in es that are contained inside the expression e.
let rec exprsInExpr es (e : Z3.Expr) : Set<Z3.Expr> = 
    // Is this expression the same as any expressions in es?
    let self = es |> Set.filter e.Equals
    
    // Are any of the expressions inside e the same?
    let inner = 
        e.Args
        |> Set.ofArray
        |> unionMap (exprsInExpr es)
    self + inner

/// Extracts the post-states of the given environment.
let aftersOfEnv map = 
    map
    |> Map.toSeq
    |> Seq.map (snd
                >> eraseVar
                >> fun v -> v.PostExpr)
    |> Set.ofSeq

/// Extracts all the post-state variables in the model.
let aftersInModel model = 
    let g = aftersOfEnv model.Globals
    let l = aftersOfEnv model.Locals
    g + l

/// For a given expression, finds all the bound post-state variables.
let aftersInExpr model = exprsInExpr (aftersInModel model)

/// For a given expression, finds all the unbound post-state variables.
let aftersNotInExpr model expr = aftersInModel model - aftersInExpr model expr

/// Substitutes a different version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarTo sel env (expr : #Z3.Expr) var = 
    lookupVar env var |> either (fst
                                 >> eraseVar
                                 >> fun v -> expr.Substitute(v.Expr, sel v)) (fun _ -> expr :> Z3.Expr)

/// Substitutes the before version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarToBefore e = envVarTo (fun v -> v.PreExpr) e

/// Substitutes the after version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarToAfter e = envVarTo (fun v -> v.PostExpr) e

/// Performs the given substitution for all variables in the
/// given sequence.
let subAllInSeq env sq sub expr = Seq.fold (sub env) expr sq

/// Performs the given substitution for all variables in the
/// environment.
let subAllInEnv env = 
    // TODO(CaptainHayashi): the conversion to LVIdent is indicative of
    // the lack of pointer support, and needs to go when we add it.
    subAllInSeq env (env
                     |> Map.toSeq
                     |> Seq.map (fst >> LVIdent))

/// Performs the given substitution for all variables in the model.
let subAllInModel model sub expr = 
    expr
    |> subAllInEnv model.Globals sub
    |> subAllInEnv model.Locals sub

(*
 * Expression types
 *)

type Const =
    | Unmarked of string
    | Before of string
    | After of string
    | Frame of string * int

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

(*
 * Expression constructors
 *)

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

let mkNot =
    // Simplify obviously false or true exprs to their negation.
    function | BTrue -> BFalse
             | BFalse -> BTrue
             | BNot x -> x
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
let rec boolSubVarsInEnv vfun =
    function 
    | BConst x -> vfun.BSub x
    | BTrue -> BTrue
    | BFalse -> BFalse
    | BAnd xs -> BAnd (List.map (boolSubVarsInEnv vfun) xs)
    | BOr xs -> BOr (List.map (boolSubVarsInEnv vfun) xs)
    | BImplies (x, y) -> BImplies (boolSubVarsInEnv vfun x,
                                   boolSubVarsInEnv vfun y)
    | BEq (x, y) -> BEq (subVarsInEnv vfun x,
                         subVarsInEnv vfun y)
    | BGt (x, y) -> BGt (arithSubVarsInEnv vfun x,
                         arithSubVarsInEnv vfun y)
    | BGe (x, y) -> BGe (arithSubVarsInEnv vfun x,
                         arithSubVarsInEnv vfun y)
    | BLe (x, y) -> BLe (arithSubVarsInEnv vfun x,
                         arithSubVarsInEnv vfun y)
    | BLt (x, y) -> BLt (arithSubVarsInEnv vfun x,
                         arithSubVarsInEnv vfun y)
    | BNot x -> BNot (boolSubVarsInEnv vfun x)

/// Substitutes all variables with the given substitution function
/// for the given arithmetic expression.
and arithSubVarsInEnv vfun =
    function 
    | AConst x -> vfun.ASub x
    | AInt i -> AInt i
    | AAdd xs -> AAdd (List.map (arithSubVarsInEnv vfun) xs)
    | ASub xs -> ASub (List.map (arithSubVarsInEnv vfun) xs)
    | AMul xs -> AMul (List.map (arithSubVarsInEnv vfun) xs)
    | ADiv (x, y) -> ADiv (arithSubVarsInEnv vfun x,
                           arithSubVarsInEnv vfun y)

/// Substitutes all variables with the given substitution function for the
/// given expression.
and subVarsInEnv vfun =
    function
    | AExpr a -> arithSubVarsInEnv vfun a |> AExpr
    | BExpr b -> boolSubVarsInEnv vfun b |> BExpr

(*
 * Variable marking (special case of variable substitution)
 *)

/// Lifts a marking function to a substitution function table.
let liftMarker marker vset =
    let gfun = function | Unmarked s when Set.contains s vset -> marker s
                        | x -> x
    {ASub = (gfun >> AConst)
     BSub = (gfun >> BConst)}

/// Marks all variables in the given environment with the given marking
/// functions / pre-states for the given arithmetic expression.
let arithMarkVarsInEnv marker vset =
    arithSubVarsInEnv (liftMarker marker vset)

/// Marks all variables in the given environment with the given marking
/// functions / pre-states for the given Boolean expression.
let boolMarkVarsInEnv marker vset =
    boolSubVarsInEnv (liftMarker marker vset)

/// Marks all variables in the given set with the given marking
/// functions / pre-states for the given arbitrary expression.
let markVarsInEnv marker vset =
    subVarsInEnv (liftMarker marker vset)
