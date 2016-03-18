/// <summary>
///     Utilities and types for working with expressions.
/// </summary>
module Starling.Core.Expr

open Starling.Utils
open Starling.Core.Var


/// <summary>
///     Expression types.
/// </summary>
[<AutoOpen>]
module Types =
    type Const =
        /// <summary>
        ///     A variable that has not yet been assigned to the pre-state or
        ///     the post-state.
        /// </summary>
        | Unmarked of string
        /// <summary>
        ///     A variable belonging to the pre-state of a command.
        /// </summary>
        | Before of string
        /// <summary>
        ///     A variable belonging to the post-state of a command.
        /// </summary>
        | After of string
        /// <summary>
        ///     A variable belonging to part of the goal term.
        ///     The bigint is used to ensure variables in one goal
        ///     view are separate from variables in another.
        /// </summary>
        | Goal of bigint * string
        /// <summary>
        ///     A variable belonging to an intermediate state of a composed
        ///     command.
        ///     The bigint is used to ensure different intermediate
        ///     states are separate from each other.
        /// </summary>
        | Intermediate of bigint * string

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

    /// Type for fresh variable generators.
    type FreshGen = bigint ref


// This is here as it is used by the pretty-printers.

/// Converts a Starling constant into a string.
let constToString =
    function
    | Unmarked s -> s
    | Before s -> sprintf "%s!before" s
    | After s -> sprintf "%s!after" s
    | Intermediate (i, s) -> sprintf "%s!int!%A" s i
    | Goal (i, s) -> sprintf "%s!goal!%A" s i


/// <summary>
///     Pretty printers for expressions.
///
///     <para>
///         These are deliberately made to look like the Z3 equivalent.
///     </para>
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// Creates an S-expression from an operator string, operand print function, and
    /// sequence of operands.
    let sexpr op pxs =
        Seq.map pxs
        >> scons (String op)
        >> hsep
        >> parened

    /// Pretty-prints an arithmetic expression.
    let rec printArithExpr =
        function
        | AConst c -> c |> constToString |> String
        | AInt i -> i |> sprintf "%i" |> String
        | AAdd xs -> sexpr "+" printArithExpr xs
        | ASub xs -> sexpr "-" printArithExpr xs
        | AMul xs -> sexpr "*" printArithExpr xs
        | ADiv (x, y) -> sexpr "/" printArithExpr [x; y]

    /// Pretty-prints a Boolean expression.
    and printBoolExpr =
        function
        | BConst c -> c |> constToString |> String
        | BTrue -> String "true"
        | BFalse -> String "false"
        | BAnd xs -> sexpr "and" printBoolExpr xs
        | BOr xs -> sexpr "or" printBoolExpr xs
        | BImplies (x, y) -> sexpr "=>" printBoolExpr [x; y]
        | BEq (x, y) -> sexpr "=" printExpr [x; y]
        | BGt (x, y) -> sexpr ">" printArithExpr [x; y]
        | BGe (x, y) -> sexpr ">=" printArithExpr [x; y]
        | BLe (x, y) -> sexpr "<=" printArithExpr [x; y]
        | BLt (x, y) -> sexpr "<" printArithExpr [x; y]
        | BNot x -> sexpr "not" printBoolExpr [x]

    /// Pretty-prints an expression.
    and printExpr =
        function
        | AExpr a -> printArithExpr a
        | BExpr b -> printBoolExpr b


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
        // A Boolean equality between something and True reduces to that something.
        | x, BTrue          -> x
        | BTrue, x          -> x
        | x, BFalse         -> simp (BNot x)
        | BFalse, x         -> simp (BNot x)
        | x, y              -> BEq(BExpr x, BExpr y)
    | x -> x

/// Returns true if the expression is definitely false.
/// This is sound, but not complete.
let isFalse =
    simp >> 
    function
    | BFalse -> true
    | _      -> false
   
let isTrue =
    simp >> 
    function
    | BTrue -> true
    | _     -> false
      
/// Extracts the name from a Starling constant.
let stripMark =
    function
    | Unmarked s -> s
    | Before s -> s
    | Intermediate (i, s) -> s
    | After s -> s
    | Goal (i, s) -> s

(*
 * Expression constructors
 *)

/// Creates an unmarked arithmetic constant.
let aUnmarked c = c |> Unmarked |> AConst

/// Creates an after-marked arithmetic constant.
let aAfter c = c |> After |> AConst

/// Creates a before-marked arithmetic constant.
let aBefore c = c |> Before |> AConst

/// Creates an intermediate-marked Boolean constant.
let aInter i c = (i, c) |> Intermediate |> AConst

/// Creates an unmarked Boolean constant.
let bUnmarked c = c |> Unmarked |> BConst

/// Creates an after-marked Boolean constant.
let bAfter c = c |> After |> BConst

/// Creates a before-marked Boolean constant.
let bBefore c = c |> Before |> BConst

/// Creates an intermediate-marked Boolean constant.
let bInter i c = (i, c) |> Intermediate |> BConst

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

/// Creates a new fresh generator.
let freshGen () = ref 0I

/// Takes a fresh number out of the generator.
/// This method is NOT thread-safe.
let getFresh fg =
    let result = !fg
    fg := !fg + 1I
    result

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

/// <summary>
///     Returns true if two expressions are definitely negations of each
///     other.
///
///     <para>
///         This is sound, but not complete.  It should only be used for
///         optimisations.
///     </para>
/// </summary>
/// <param name="x">
///     The first expression to check.
/// </param>
/// <param name="y">
///     The second expression to check.
/// </param>
/// <returns>
///     True only if (but not if!) <paramref name="x" /> and
///     <paramref name="y" /> negate each other.
/// </returns>
let negates x y =
    let sx, sy = simp x, simp y
    // The || is intentional, to try and compensate for deficiencies in simp.
    (x = mkNot y) || (y = mkNot x)


(*
 * Composition
 *)

/// <summary>
///     Finds the highest intermediate stage number in an Arithmetic
///     expression.
///     Returns one higher.
/// </summary>
/// <param name="_arg1">
///     The <c>ArithExpr</c> to investigate.
/// </param>
/// <returns>
///     The next available intermediate stage number.
///     If the expression has no intermediate stages, we return 0.
/// </returns>
let rec nextIntIntermediate =
    function
    | AConst (Intermediate (n, _)) -> n + 1I
    | AConst _ | AInt _ -> 0I
    | AAdd xs | ASub xs | AMul xs ->
        xs |> Seq.map nextIntIntermediate |> Seq.fold (curry bigint.Max) 0I
    | ADiv (x, y) ->
        bigint.Max (nextIntIntermediate x, nextIntIntermediate y)

/// <summary>
///     Finds the highest intermediate stage number in a Boolean expression.
///     Returns one higher.
/// </summary>
/// <param name="_arg1">
///     The <c>BoolExpr</c> to investigate.
/// </param>
/// <returns>
///     The next available intermediate stage number.
///     If the expression has no intermediate stages, we return 0.
/// </returns>
and nextBoolIntermediate =
    function
    | BConst (Intermediate (n, _)) -> n + 1I
    | BConst _ -> 0I
    | BAnd xs | BOr xs ->
        xs |> Seq.map nextBoolIntermediate |> Seq.fold (curry bigint.Max) 0I
    | BImplies (x, y) ->
        bigint.Max (nextBoolIntermediate x, nextBoolIntermediate y)
    | BNot x -> nextBoolIntermediate x
    | BGt (x, y) | BLt (x, y) | BGe (x, y) | BLe (x, y) ->
        bigint.Max (nextIntIntermediate x, nextIntIntermediate y)
    | BEq (x, y) ->
        bigint.Max (nextIntermediate x, nextIntermediate y)
    | BTrue | BFalse -> 0I

/// <summary>
///     Finds the highest intermediate stage number in an expression.
///     Returns one higher.
/// </summary>
/// <param name="_arg1">
///     The <c>Expr</c> to investigate.
/// </param>
/// <returns>
///     The next available intermediate stage number.
///     If the expression has no intermediate stages, we return 0.
/// </returns>
and nextIntermediate =
    function
    | AExpr x -> nextIntIntermediate x
    | BExpr x -> nextBoolIntermediate x


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
