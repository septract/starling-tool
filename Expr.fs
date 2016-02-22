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
 
/// Partial pattern that matches a Boolean equality on arithmetic expressions.
let (|BAEq|_|) =
    function
    | BEq (AExpr x, AExpr y) -> Some (x, y)
    | _ -> None

/// Partial pattern that matches a Boolean equality on Boolean expressions.
let (|BBEq|_|) =
    function
    | BEq (BExpr x, BExpr y) -> Some (x, y)
    | _ -> None

/// Recursively simplify a formula
let rec simp ax =
    match ax with 
    | BNot (x) -> 
        match simp x with 
        | BTrue      -> BFalse
        | BFalse     -> BTrue
        | BNot x     -> x
        | BGt (x, y) -> BLe (x, y)
        | BGe (x, y) -> BLt (x, y)
        | BLe (x, y) -> BGt (x, y)
        | BLt (x, y) -> BGe (x, y)
        //Following, all come from DeMorgan 
        | BAnd xs        -> simp (BOr (List.map BNot xs))
        | BOr xs         -> simp (BAnd (List.map BNot xs)) 
        | BImplies (x,y) -> simp (BAnd [x; BNot y]) 
        | y          -> BNot y
    // x = x is always true.
    | BEq (x, y) when x = y -> BTrue
    // As are x >= x, and x <= x.
    | BGe (x, y) 
    | BLe (x, y) when x = y -> BTrue
    | BImplies (x, y) ->
        match simp x, simp y with
        | BFalse, _ 
        | _, BTrue      -> BTrue
        | BTrue, y      -> y
        | x, BFalse     -> simp (BNot x)
        | x, y          -> BImplies(x,y)
    | BOr xs -> 
        match foldFastTerm  
                (fun s x ->
                  match simp x with 
                  | BTrue  -> None
                  | BFalse -> Some s   
                  | BOr ys -> Some (ys @ s)  
                  | y      -> Some (y :: s)
                )
                [] 
                xs with 
        | Some []  -> BFalse
        | Some [x] -> x
        | Some xs  -> BOr (List.rev xs)
        | None     -> BTrue
    // An and is always true if everything in it is always true.
    | BAnd xs -> 
        match foldFastTerm  
                (fun s x ->
                  match simp x with 
                  | BFalse  -> None
                  | BTrue   -> Some s     
                  | BAnd ys -> Some (ys @ s)
                  | y       -> Some (y :: s)
                )
                [] 
                xs with 
        | Some []  -> BTrue
        | Some [x] -> x 
        | Some xs  -> BAnd (List.rev xs)
        | None     -> BFalse
    // A Boolean equality between two contradictions or tautologies is always true.
    | BBEq (x, y)  -> 
        match simp x, simp y with
        | BFalse, BFalse 
        | BTrue, BTrue      -> BTrue
        | BTrue, BFalse 
        | BFalse, BTrue     -> BFalse   
        | x, y              -> BEq(BExpr x, BExpr y)
    | x -> x

/// Returns true if the expression is definitely false.
/// This is sound, but not complete.
let isFalse =
    simp >> 
    function
    // False is always false.
    | BFalse -> true
    | _      -> false
   
let isTrue =
    simp >> 
    function
    // False is always false.
    | BTrue -> true
    | _      -> false
      
/// Extracts the name from a Starling constant.
let stripMark =
    function
    | Unmarked s -> s
    | Before s -> s
    | After s -> s
    | Frame (i, s) -> s

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
let mkAnd = BAnd >> simp

/// Slightly optimised version of ctx.MkOr.
/// Returns false for the empty set, and x for the singleton set {x}.
let mkOr  = BOr >> simp

/// Makes an And from a pair of two expressions.
let mkAnd2 l r = mkAnd [l ; r]

/// Makes an Or from a pair of two expressions.
let mkOr2 l r = mkOr [l ; r]

/// Symbolically inverts a Boolean expression.
let mkNot = BNot >> simp

/// Makes not-equals.
let mkNeq l r = mkEq l r |> mkNot

/// Makes an implication from a pair of two expressions.
let mkImplies l r = BImplies (l, r) |> simp

/// Makes an Add out of a pair of two expressions.
let mkAdd2 l r = AAdd [ l; r ]
/// Makes a Sub out of a pair of two expressions.
let mkSub2 l r = ASub [ l; r ]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 l r = AMul [ l; r ]


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

(*
 * Active patterns
 *)

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

/// Partial pattern that matches a Boolean expression in terms of exactly one /
/// constant.
let rec (|ConstantBoolFunction|_|) = varsInBool >> onlyOne

/// Partial pattern that matches a Boolean expression in terms of exactly one /
/// constant.
let rec (|ConstantArithFunction|_|) = varsInArith >> onlyOne
