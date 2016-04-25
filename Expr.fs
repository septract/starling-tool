/// <summary>
///     Utilities and types for working with expressions.
/// </summary>
module Starling.Core.Expr

open Starling.Collections
open Starling.Utils
open Starling.Core.Var


/// <summary>
///     Expression types.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A variable with no marking.
    /// </summary>
    type Var = string

    /// <summary>
    ///     A variable that has been marked according to whether it comes
    ///     from the pre-state, the post-state, an intermediate state, or
    ///     a possibly-external observation in the goal view.
    /// </summary>
    type MarkedVar =
        /// <summary>
        ///     A variable that has not yet been assigned to the pre-state or
        ///     the post-state.
        /// </summary>
        | Unmarked of Var
        /// <summary>
        ///     A variable belonging to the pre-state of a command.
        /// </summary>
        | Before of Var
        /// <summary>
        ///     A variable belonging to the post-state of a command.
        /// </summary>
        | After of Var
        /// <summary>
        ///     A variable belonging to part of the goal term.
        ///     The bigint is used to ensure variables in one goal
        ///     view are separate from variables in another.
        /// </summary>
        | Goal of bigint * Var
        /// <summary>
        ///     A variable belonging to an intermediate state of a composed
        ///     command.
        ///     The bigint is used to ensure different intermediate
        ///     states are separate from each other.
        /// </summary>
        | Intermediate of bigint * Var

    /// <summary>
    ///     An expression of arbitrary type.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the expression.
    /// </typeparam>
    type Expr<'var> = Typed<IntExpr<'var>, BoolExpr<'var>>

    /// <summary>
    ///     An integral expression.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and IntExpr<'var> =
        | AVar of 'var
        | AInt of int64
        | AAdd of IntExpr<'var> list
        | ASub of IntExpr<'var> list
        | AMul of IntExpr<'var> list
        | ADiv of IntExpr<'var> * IntExpr<'var>

    /// <summary>
    ///     A Boolean expression.
    /// </summary>
    /// <typeparam name="var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and BoolExpr<'var> =
        | BVar of 'var
        | BTrue
        | BFalse
        | BAnd of BoolExpr<'var> list
        | BOr of BoolExpr<'var> list
        | BImplies of BoolExpr<'var> * BoolExpr<'var>
        | BEq of Expr<'var> * Expr<'var>
        | BGt of IntExpr<'var> * IntExpr<'var>
        | BGe of IntExpr<'var> * IntExpr<'var>
        | BLe of IntExpr<'var> * IntExpr<'var>
        | BLt of IntExpr<'var> * IntExpr<'var>
        | BNot of BoolExpr<'var>

    /// <summary>
    ///     A variable reference that may be symbolic.
    ///
    ///     <para>
    ///         A symbolic variable is one whose value depends on an
    ///         uninterpreted function of multiple 'real' Starling variables.
    ///         It allows encoding into Starling of patterns of variable usage
    ///         Starling doesn't yet understand natively.
    ///     </para>
    /// </summary>
    /// <typeparam name="var">
    ///     The non-symbolic variable <c>Sym</c> wraps.
    /// </typeparam>
    type Sym<'var> =
        /// <summary>
        ///     A symbolic variable, predicated over multiple expressions.
        ///     The symbol itself is the name inside the <c>Func</c>.
        /// </summary>
        | Sym of Func<Expr<Sym<'var>>>
        /// <summary>
        ///     A regular, non-symbolic variable.
        | Reg of 'var

    /// <summary>
    ///     An expression of arbitrary type using <c>Var</c>s.
    /// </summary>
    type VExpr = Expr<Var>
    /// <summary>
    ///     An expression of Boolean type using <c>Var</c>s.
    /// </summary>
    type VBoolExpr = BoolExpr<Var>
    /// <summary>
    ///     An expression of integral type using <c>Var</c>s.
    /// </summary>
    type VIntExpr = IntExpr<Var>

    /// <summary>
    ///     An expression of arbitrary type using <c>MarkedVar</c>s.
    /// </summary>
    type MExpr = Expr<MarkedVar>
    /// <summary>
    ///     An expression of Boolean type using <c>MarkedVar</c>s.
    /// </summary>
    type MBoolExpr = BoolExpr<MarkedVar>
    /// <summary>
    ///     An expression of integral type using <c>MarkedVar</c>s.
    /// </summary>
    type MIntExpr = IntExpr<MarkedVar>

    /// <summary>
    ///     An expression of arbitrary type using symbolic <c>Var</c>s.
    /// </summary>
    type SVExpr = Expr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of Boolean type using symbolic <c>Var</c>s.
    /// </summary>
    type SVBoolExpr = BoolExpr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of integral type using <c>Var</c>s.
    /// </summary>
    type SVIntExpr = IntExpr<Sym<MarkedVar>>

    /// <summary>
    ///     An expression of arbitrary type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMExpr = Expr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of Boolean type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMBoolExpr = BoolExpr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of integral type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMIntExpr = IntExpr<Sym<MarkedVar>>


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
    let rec printIntExpr pVar =
        function
        | AVar c -> pVar c
        | AInt i -> i |> sprintf "%i" |> String
        | AAdd xs -> sexpr "+" (printIntExpr pVar) xs
        | ASub xs -> sexpr "-" (printIntExpr pVar) xs
        | AMul xs -> sexpr "*" (printIntExpr pVar) xs
        | ADiv (x, y) -> sexpr "/" (printIntExpr pVar) [x; y]

    /// Pretty-prints a Boolean expression.
    and printBoolExpr pVar =
        function
        | BVar c -> pVar c
        | BTrue -> String "true"
        | BFalse -> String "false"
        | BAnd xs -> sexpr "and" (printBoolExpr pVar)xs
        | BOr xs -> sexpr "or" (printBoolExpr pVar) xs
        | BImplies (x, y) -> sexpr "=>" (printBoolExpr pVar) [x; y]
        | BEq (x, y) -> sexpr "=" (printExpr pVar) [x; y]
        | BGt (x, y) -> sexpr ">" (printIntExpr pVar) [x; y]
        | BGe (x, y) -> sexpr ">=" (printIntExpr pVar) [x; y]
        | BLe (x, y) -> sexpr "<=" (printIntExpr pVar) [x; y]
        | BLt (x, y) -> sexpr "<" (printIntExpr pVar) [x; y]
        | BNot x -> sexpr "not" (printBoolExpr pVar) [x]

    /// Pretty-prints an expression.
    and printExpr pVar =
        function
        | Int a -> printIntExpr pVar a
        | Bool b -> printBoolExpr pVar b

    /// <summary>
    ///     Pretty-prints a <c>Sym</c>.
    /// </summary>
    /// <param name="pReg">
    ///     Pretty printer to use for regular variables.
    /// </param>
    /// <returns>
    ///     A function taking <c>Sym</c>s and returning pretty-printer
    ///     <c>Command</c>s.
    /// </returns>
    let rec printSym pReg =
        function
        | Sym { Name = sym ; Params = regs } ->
            func (sprintf "%%{%s}" sym) (Seq.map (printExpr (printSym pReg)) regs)
        | Reg reg -> pReg reg

    /// Pretty-prints a MExpr.
    let printMExpr = printExpr (constToString >> String)
    /// Pretty-prints a SMExpr.
    let printSMExpr = printExpr (printSym (constToString >> String))
    /// Pretty-prints a MBoolExpr.
    let printSMBoolExpr = printBoolExpr (printSym (constToString >> String))
    /// Pretty-prints a MBoolExpr.
    let printMBoolExpr = printBoolExpr (constToString >> String)
    /// Pretty-prints a MIntExpr.
    let printMIntExpr = printIntExpr (constToString >> String)

/// Partial pattern that matches a Boolean equality on arithmetic expressions.
let (|BAEq|_|) =
    function
    | BEq (Int x, Int y) -> Some (x, y)
    | _ -> None

/// Partial pattern that matches a Boolean equality on Boolean expressions.
let (|BBEq|_|) =
    function
    | BEq (Bool x, Bool y) -> Some (x, y)
    | _ -> None

/// Recursively simplify a formula
/// Note: this does _not_ simplify variables.
let rec simp (ax : BoolExpr<'var>) : BoolExpr<'var> =
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
        | x, y              -> BEq(Bool x, Bool y)
    | x -> x

/// Returns true if the expression is definitely false.
/// This is sound, but not complete.
let isFalse expr =
    match (simp expr) with
    | BFalse -> true
    | _      -> false
   
let isTrue expr =
    match (simp expr) with
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

/// Creates an unmarked integer variable.
let iUnmarked c = c |> Unmarked |> AVar

/// Creates an unmarked integer sym-variable.
let siUnmarked c = c |> Unmarked |> Reg |> AVar

/// Creates an after-marked integer variable.
let iAfter c = c |> After |> AVar

/// Creates an after-marked integer sym-variable.
let siAfter c = c |> After |> Reg |> AVar

/// Creates a before-marked integer variable.
let iBefore c = c |> Before |> AVar

/// Creates an before-marked integer sym-variable.
let siBefore c = c |> Before |> Reg |> AVar

/// Creates a goal-marked integer variable.
let iGoal i c = (i, c) |> Goal |> AVar

/// Creates a goal-marked integer sym-variable.
let siGoal i c = (i, c) |> Goal |> Reg |> AVar

/// Creates an intermediate-marked integer variable.
let iInter i c = (i, c) |> Intermediate |> AVar

/// Creates an intermediate-marked integer sym-variable.
let siInter i c = (i, c) |> Intermediate |> Reg |> AVar

/// Creates an unmarked Boolean variable.
let bUnmarked c = c |> Unmarked |> BVar

/// Creates an unmarked Boolean sym-variable.
let sbUnmarked c = c |> Unmarked |> Reg |> BVar

/// Creates an after-marked Boolean variable.
let bAfter c = c |> After |> BVar

/// Creates an before-marked Boolean sym-variable.
let sbAfter c = c |> After |> Reg |> BVar

/// Creates a before-marked Boolean variable.
let bBefore c = c |> Before |> BVar

/// Creates an before-marked Boolean sym-variable.
let sbBefore c = c |> Before |> Reg |> BVar

/// Creates a goal-marked Boolean variable.
let bGoal i c = (i, c) |> Goal |> BVar

/// Creates a goal-marked Inter sym-variable.
let sbGoal i c = (i, c) |> Goal |> Reg |> BVar

/// Creates an intermediate-marked Boolean variable.
let bInter i c = (i, c) |> Intermediate |> BVar

/// Creates an intermediate-marked Boolean sym-variable.
let sbInter i c = (i, c) |> Intermediate |> Reg |> BVar

/// Converts a typed string to an expression.
let mkVarExp marker (ts : CTyped<string>) =
    match ts with
    | Int s -> s |> marker |> AVar |> Int
    | Bool s -> s |> marker |> BVar |> Bool

/// Converts a VarMap to a sequence of expressions.
let varMapToExprs marker vm =
    vm |> Map.toSeq |> Seq.map (fun (name, ty) -> mkVarExp marker (withType ty name))

(* The following are just curried versions of the usual constructors. *)

/// Curried wrapper over BGt.
let mkGt a b = BGt (a, b)
/// Curried wrapper over BGe.
let mkGe a b = BGe (a, b)
/// Curried wrapper over BLt.
let mkLt a b = BLt (a, b)
/// Curried wrapper over BLe.
let mkLe a b = BLe (a, b)

/// Curried wrapper over BEq.
let mkEq a b = BEq (a, b)

/// Makes an arithmetic equality.
let iEq a b = BEq (Int a, Int b)

/// Makes a Boolean equality.
let bEq a b = BEq (Bool a, Bool b)

/// Curried wrapper over ADiv.
let mkDiv a b = ADiv (a, b)

/// Slightly optimised version of ctx.MkAnd.
/// Returns true for the empty array, and x for the singleton set {x}.
let mkAnd xs = simp (BAnd xs)

/// Slightly optimised version of ctx.MkOr.
/// Returns false for the empty set, and x for the singleton set {x}.
let mkOr xs = simp (BOr xs)

/// Makes an And from a pair of two expressions.
let mkAnd2 l r = mkAnd [l ; r]

/// Makes an Or from a pair of two expressions.
let mkOr2 l r = mkOr [l ; r]

/// Symbolically inverts a Boolean expression.
let mkNot x = simp (BNot x)

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

/// <summary>
///     Returns a set of all variables used in an arithmetic expression,
///     coupled with type.
/// </summary>
let rec varsInInt =
    function
    | AVar c -> Set.singleton (Typed.Int c)
    | AInt _ -> Set.empty
    | AAdd xs -> xs |> Seq.map varsInInt |> Set.unionMany
    | ASub xs -> xs |> Seq.map varsInInt |> Set.unionMany
    | AMul xs -> xs |> Seq.map varsInInt |> Set.unionMany
    | ADiv (x, y) -> Set.union (varsInInt x) (varsInInt y)

/// <summary>
///     Returns a set of all variables used in a Boolean expression,
///     coupled with type.
/// </summary>
and varsInBool =
    function
    | BVar c -> Set.singleton (Typed.Bool c)
    | BTrue -> Set.empty
    | BFalse -> Set.empty
    | BAnd xs -> xs |> Seq.map varsInBool |> Set.unionMany
    | BOr xs -> xs |> Seq.map varsInBool |> Set.unionMany
    | BImplies (x, y) -> Set.union (varsInBool x) (varsInBool y)
    | BEq (x, y) -> Set.union (varsIn x) (varsIn y)
    | BGt (x, y) -> Set.union (varsInInt x) (varsInInt y)
    | BGe (x, y) -> Set.union (varsInInt x) (varsInInt y)
    | BLe (x, y) -> Set.union (varsInInt x) (varsInInt y)
    | BLt (x, y) -> Set.union (varsInInt x) (varsInInt y)
    | BNot x -> varsInBool x

/// Returns a set of all variables used in an expression.
and varsIn =
    function
    | Int a -> varsInInt a
    | Bool b -> varsInBool b

/// <summary>
///     Extracts all of the regular variables in a symbolic variable.
/// </summary>
/// <param name="sym">
///     The symbolic variable to destructure.
/// </param>
/// <typeparam name="var">
///     The type of regular variables in the symbolic variable.
/// </typeparam>
/// <returns>
///     A list of regular variables bound in a symbolic variable.
/// </returns>
let rec regularVarsInSym
  (sym : Sym<'var>)
  : 'var list =
    match sym with
    | Reg x -> [x]
    | Sym { Params = xs } ->
        xs
        |> List.map (varsIn
                     >> Set.toList
                     >> List.map (valueOf >> regularVarsInSym)
                     >> List.concat)
        |> List.concat


(*
 * Composition
 *)

/// <summary>
///     Finds the highest intermediate stage number in an integral
///     expression.
///     Returns one higher.
/// </summary>
/// <param name="_arg1">
///     The <c>IntExpr</c> to investigate.
/// </param>
/// <returns>
///     The next available intermediate stage number.
///     If the expression has no intermediate stages, we return 0.
/// </returns>
let rec nextIntIntermediate =
    function
    | AVar (Reg (Intermediate (n, _))) -> n + 1I
    | AVar (Sym { Params = xs } ) -> 
        xs |> Seq.map nextIntermediate |> Seq.fold (curry bigint.Max) 0I
    | AVar _ | AInt _ -> 0I
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
    | BVar (Reg (Intermediate (n, _))) -> n + 1I
    | BVar (Sym { Params = xs } ) ->
        xs |> Seq.map nextIntermediate |> Seq.fold (curry bigint.Max) 0I
    | BVar _ -> 0I
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
    | Int x -> nextIntIntermediate x
    | Bool x -> nextBoolIntermediate x


(*
 * Active patterns
 *)

/// Categorises integral expressions into simple or compound.
let (|SimpleInt|CompoundInt|) =
    function
    | AVar _ | AInt _ -> SimpleInt
    | _ -> CompoundInt

/// Categorises Boolean expressions into simple or compound.
let (|SimpleBool|CompoundBool|) =
    function
    | BVar _ | BTrue | BFalse -> SimpleBool
    | _ -> CompoundBool

/// Categorises expressions into simple or compound.
let (|SimpleExpr|CompoundExpr|) =
    function
    | Bool (SimpleBool) -> SimpleExpr
    | Int (SimpleInt) -> SimpleExpr
    | _ -> CompoundExpr

/// Partial pattern that matches a Boolean expression in terms of exactly one /
/// constant.
let rec (|ConstantBoolFunction|_|) x =
    x |> varsInBool |> Seq.map valueOf |> onlyOne

/// Partial pattern that matches a Boolean expression in terms of exactly one /
/// constant.
let rec (|ConstantIntFunction|_|) x =
    x |>varsInInt |> Seq.map valueOf |> onlyOne
