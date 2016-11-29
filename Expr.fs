/// <summary>
///     Utilities and types for working with expressions.
/// </summary>
module Starling.Core.Expr

open Starling.Utils
open Starling.Core.TypeSystem


/// <summary>
///     Expression types.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     An expression of arbitrary type.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    type Expr<'Var> when 'Var : equality =
        Typed<IntExpr<'Var>, BoolExpr<'Var>, ArrayExpr<'Var>>

    /// <summary>
    ///     An integral expression.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and IntExpr<'Var> when 'Var : equality =
        | IVar of 'Var
        | IIdx of eltype : Type
                * length : int option
                * arr : ArrayExpr<'Var>
                * idx : IntExpr<'Var>
        | IInt of int64
        | IAdd of IntExpr<'Var> list
        | ISub of IntExpr<'Var> list
        | IMul of IntExpr<'Var> list
        | IDiv of IntExpr<'Var> * IntExpr<'Var>
        | IMod of IntExpr<'Var> * IntExpr<'Var>
        override this.ToString () = sprintf "%A" this

    /// <summary>
    ///     A Boolean expression.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and BoolExpr<'Var> when 'Var : equality =
        | BVar of 'Var
        | BIdx of eltype : Type
                * length : int option
                * arr : ArrayExpr<'Var>
                * idx : IntExpr<'Var>
        | BTrue
        | BFalse
        | BAnd of BoolExpr<'Var> list
        | BOr of BoolExpr<'Var> list
        | BImplies of BoolExpr<'Var> * BoolExpr<'Var>
        | BEq of Expr<'Var> * Expr<'Var>
        | BGt of IntExpr<'Var> * IntExpr<'Var>
        | BGe of IntExpr<'Var> * IntExpr<'Var>
        | BLe of IntExpr<'Var> * IntExpr<'Var>
        | BLt of IntExpr<'Var> * IntExpr<'Var>
        | BNot of BoolExpr<'Var>
        override this.ToString () = sprintf "%A" this

    /// <summary>
    ///     An array expression.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and ArrayExpr<'Var> when 'Var : equality =
        /// <summary>An array variable reference.</summary>
        | AVar of 'Var
        /// <summary>
        ///     An index into an array <c>arr</c> of type <c>eltype[length]</c>.
        /// </summary>
        | AIdx of eltype : Type
                * length : int option
                * arr : ArrayExpr<'Var>
                * idx : IntExpr<'Var>
        /// <summary>
        ///     A functional update of an array <c>arr</c> of type
        ///     <c>eltype[length]</c>, overriding index <c>idx</c> with value
        ///     <c>var</c>.
        /// </summary>
        | AUpd of eltype : Type
                * length : int option
                * arr : ArrayExpr<'Var>
                * idx : IntExpr<'Var>
                * nval : Expr<'Var>

    /// Type for fresh variable generators.
    type FreshGen = bigint ref


/// <summary>
///     Pretty printers for expressions.
///
///     <para>
///         These are deliberately made to look like the Z3 equivalent.
///     </para>
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    let svexpr (op : string) (pxs : 'x -> Doc) (x : 'x seq) : Doc =
      let mapped = Seq.map pxs x
      let sep = ivsep mapped in
      let head = HSep([(String "("); (String op)], Nop)
      vsep [head; sep; (String ")")]

    /// Creates an S-expression from an operator string and sequence of operand
    /// documents.
    let cmdSexpr (op : string) : Doc seq -> Doc =
        scons (String op) >> hsep >> parened

    /// Creates an S-expression from an operator string, operand print function, and
    /// sequence of operands.
    let sexpr (op : string) (pxs : 'x -> Doc) : 'x seq -> Doc =
        cmdSexpr op << Seq.map pxs

    /// Pretty-prints an array subscript.
    let rec printIdx
      (pVar : 'Var -> Doc)
      (arr : ArrayExpr<'Var>)
      (idx : IntExpr<'Var>) : Doc =
        cmdSexpr "select" [ printIntExpr pVar idx; printArrayExpr pVar arr ]

    /// Pretty-prints an arithmetic expression.
    and printIntExpr (pVar : 'Var -> Doc) : IntExpr<'Var> -> Doc =
        function
        | IVar c -> pVar c
        | IInt i -> i |> sprintf "%i" |> String
        | IIdx (_, _, arr, idx) -> printIdx pVar arr idx
        | IAdd xs -> sexpr "+" (printIntExpr pVar) xs
        | ISub xs -> sexpr "-" (printIntExpr pVar) xs
        | IMul xs -> sexpr "*" (printIntExpr pVar) xs
        | IDiv (x, y) -> sexpr "/" (printIntExpr pVar) [x; y]
        | IMod (x, y) -> sexpr "%" (printIntExpr pVar) [x; y]

    /// Pretty-prints a Boolean expression.
    and printBoolExpr (pVar : 'Var -> Doc) : BoolExpr<'Var> -> Doc =
        function
        | BVar c -> pVar c
        | BIdx (_, _, arr, idx) -> printIdx pVar arr idx
        | BTrue -> String "true"
        | BFalse -> String "false"
        | BAnd xs -> svexpr "and" (printBoolExpr pVar) xs
        | BOr xs -> svexpr "or" (printBoolExpr pVar) xs
        | BImplies (x, y) -> svexpr "=>" (printBoolExpr pVar) [x; y]
        | BEq (x, y) -> sexpr "=" (printExpr pVar) [x; y]
        | BGt (x, y) -> sexpr ">" (printIntExpr pVar) [x; y]
        | BGe (x, y) -> sexpr ">=" (printIntExpr pVar) [x; y]
        | BLe (x, y) -> sexpr "<=" (printIntExpr pVar) [x; y]
        | BLt (x, y) -> sexpr "<" (printIntExpr pVar) [x; y]
        | BNot x -> sexpr "not" (printBoolExpr pVar) [x]

    /// Pretty-prints an array expression.
    and printArrayExpr (pVar : 'Var -> Doc) : ArrayExpr<'Var> -> Doc =
        function
        | AVar c -> pVar c
        | AIdx (_, _, arr, idx) -> printIdx pVar arr idx
        | AUpd (_, _, arr, idx, value) ->
            cmdSexpr "store"
                [ printIntExpr pVar idx
                  printExpr pVar value
                  printArrayExpr pVar arr ]

    /// Pretty-prints an expression.
    and printExpr (pVar : 'Var -> Doc) : Expr<'Var> -> Doc =
        function
        | Int i -> printIntExpr pVar i
        | Bool b -> printBoolExpr pVar b
        | Array (_, _, a) -> printArrayExpr pVar a


/// Partial pattern that matches a Boolean equality on arithmetic expressions.
let (|BAEq|_|) : BoolExpr<'var> -> (IntExpr<'var> * IntExpr<'var>) option =
    function
    | BEq (Int x, Int y) -> Some (x, y)
    | _ -> None

/// Partial pattern that matches a Boolean equality on Boolean expressions.
let (|BBEq|_|) : BoolExpr<'var> -> (BoolExpr<'var> * BoolExpr<'var>) option =
    function
    | BEq (Bool x, Bool y) -> Some (x, y)
    | _ -> None


/// Define when two Boolean expressions are trivially equal
/// Eg: (= a b)  is equivalent ot (=b a)
let rec eqBoolExpr (e1: BoolExpr<'var>) (e2:BoolExpr<'var>) : bool   =
  match e1, e2 with
  | BEq (a1,a2), BEq (b1,b2) ->
     ((a1=a2 && b1=b2) || (a1=b2 && b1=a2))
  | BNot a, BNot b -> eqBoolExpr a b
  | _ -> false


/// Remove duplicate boolean expressions
/// TODO(@septract) This is stupid, should do it more cleverly
let rec remExprDup (xs: List<BoolExpr<'var>>) : List<BoolExpr<'var>> =
  match xs with
  | (x::xs) ->
      let xs2 = remExprDup xs in
      if (List.exists (eqBoolExpr x) xs) then xs2 else x::xs2
  | x -> x


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
        | Some xs ->
           match remExprDup xs with
           | []  -> BFalse
           | [x] -> x
           | xs  -> BOr (List.rev xs)
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
        | Some xs ->
           match remExprDup xs with
           | []  -> BTrue
           | [x] -> x
           | xs  -> BAnd (List.rev xs)
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
let isFalse (expr : BoolExpr<_>) : bool =
    // NOTE: This is _not_ the same as (not isTrue).
    match (simp expr) with
    | BFalse -> true
    | _      -> false

let isTrue (expr : BoolExpr<_>) : bool =
    // NOTE: This is _not_ the same as (not isFalse).
    match (simp expr) with
    | BTrue -> true
    | _     -> false

/// Converts a typed variable to an expression.
let mkVarExp (var : CTyped<'Var>) : Expr<'Var> =
    match var with
    | CTyped.Int i -> Expr.Int (IVar i)
    | CTyped.Bool b -> Expr.Bool (BVar b)
    | CTyped.Array (eltype, length, a) -> Expr.Array (eltype, length, AVar a)

/// Converts a VarMap to a sequence of expressions.
let varMapToExprs
  (marker : string -> 'markedvar)
  : Map<string, Type> -> Expr<'markedvar> seq =
    Map.toSeq >> Seq.map (fun (name, ty) -> name |> withType ty |> mapCTyped marker |> mkVarExp)

(* The following are just curried versions of the usual constructors. *)

// TODO(CaptainHayashi): move these optimisations into an integer simplification
// function and hook it up to simp.

/// Curried wrapper over BGt.
let mkGt (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    match (a, b) with
    | IInt x, IInt y when x >  y -> BTrue
    | IInt x, IInt y when x <= y -> BFalse
    | _ -> BGt (a, b)
/// Curried wrapper over BGe.
let mkGe (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    match (a, b) with
    | IInt x, IInt y when x >= y -> BTrue
    | IInt x, IInt y when x <  y -> BFalse
    | _ -> BGe (a, b)
/// Curried wrapper over BLt.
let mkLt (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    match (a, b) with
    | IInt x, IInt y when x <  y -> BTrue
    | IInt x, IInt y when x >= y -> BFalse
    | _ -> BLt (a, b)
/// Curried wrapper over BLe.
let mkLe (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    match (a, b) with
    | IInt x, IInt y when x <= y -> BTrue
    | IInt x, IInt y when x >  y -> BFalse
    | _ -> BLe (a, b)

/// Curried wrapper over BEq.
let mkEq (a : Expr<'var>) (b : Expr<'var>) : BoolExpr<'var> = BEq (a, b)

/// Makes an arithmetic equality.
let iEq (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    BEq (Int a, Int b)

/// Makes a Boolean equality.
let bEq (a : BoolExpr<'var>) (b : BoolExpr<'var>) : BoolExpr<'var> =
    BEq (Bool a, Bool b)

/// Curried wrapper over IDiv.
let mkDiv (a : IntExpr<'var>) (b : IntExpr<'var>) : IntExpr<'var> = IDiv (a, b)

/// Curried wrapper over AMod.
let mkMod (a : IntExpr<'var>) (b : IntExpr<'var>) : IntExpr<'var> =
    match (a, b) with
    | (IInt ai, IInt bi) -> IInt (ai % bi)
    | a, b               -> IMod (a, b)

/// Slightly optimised version of ctx.MkAnd.
/// Returns true for the empty array, and x for the singleton set {x}.
let mkAnd (xs : BoolExpr<'var> list) : BoolExpr<'var> = simp (BAnd xs)

/// Slightly optimised version of ctx.MkOr.
/// Returns false for the empty set, and x for the singleton set {x}.
let mkOr (xs : BoolExpr<'var> list) : BoolExpr<'var> = simp (BOr xs)

/// Makes a BImplies
let mkImpl (a : BoolExpr<'var>) (b : BoolExpr<'var>) : BoolExpr<'var> = simp (BImplies(a, b))

/// Makes an And from a pair of two expressions.
let mkAnd2 (l : BoolExpr<'var>) (r : BoolExpr<'var>) : BoolExpr<'var> =
    mkAnd [l ; r]

/// Makes an Or from a pair of two expressions.
let mkOr2 (l : BoolExpr<'var>) (r : BoolExpr<'var>) : BoolExpr<'var> =
    mkOr [l ; r]

/// Symbolically inverts a Boolean expression.
let mkNot (x : BoolExpr<'var>) : BoolExpr<'var> = simp (BNot x)

/// Makes not-equals.
let mkNeq (l : Expr<'var>) (r : Expr<'var>) : BoolExpr<'var> =
    mkEq l r |> mkNot

/// Makes an implication from a pair of two expressions.
let mkImplies (l : BoolExpr<'var>) (r : BoolExpr<'var>) : BoolExpr<'var> =
    BImplies (l, r) |> simp

/// Makes an Add out of a pair of two expressions.
let mkAdd2 (l : IntExpr<'var>) (r : IntExpr<'var>) : IntExpr<'var> =
    match (l, r) with
    | (IInt 0L, x) | (x, IInt 0L) -> x
    | (IInt x, IInt y)            -> IInt (x + y)
    | _                           -> IAdd [ l; r ]

/// Makes a variable increment expression.
let incVar (x : 'Var) : IntExpr<'Var> = mkAdd2 (IVar x) (IInt 1L)

/// Makes an Add out of a sequence of expressions.
let mkAdd (xs : IntExpr<'var> seq) : IntExpr<'var> =
    // TODO(CaptainHayashi): produce a trimmed list, instead of mkAdd2ing.
    Seq.fold mkAdd2 (IInt 0L) xs

/// Makes a Sub out of a pair of two expressions.
let mkSub2 (l : IntExpr<'var>) (r : IntExpr<'var>) : IntExpr<'var> =
    match (l, r) with
    | (IInt x, IInt y) -> IInt (x - y)
    | _                -> ISub [ l; r ]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 (l : IntExpr<'var>) (r : IntExpr<'var>) : IntExpr<'var> =
    match (l, r) with
    | (IInt x, IInt y)            -> IInt (x * y)
    | (IInt 1L, x) | (x, IInt 1L) -> x
    | _                           -> IMul [ l; r ]


(*
 * Fresh variable generation
 *)

/// Creates a new fresh generator.
let freshGen () : FreshGen = ref 0I

/// Takes a fresh number out of the generator.
/// This method is NOT thread-safe.
let getFresh (fg : FreshGen) : bigint =
    let result = !fg
    fg := !fg + 1I
    result

(*
 * Active patterns
 *)

/// Categorises integral expressions into simple or compound.
let (|SimpleInt|CompoundInt|) : IntExpr<_> -> Choice<unit, unit> =
    function
    | IVar _ | IInt _ -> SimpleInt
    | _ -> CompoundInt

/// Categorises Boolean expressions into simple or compound.
let (|SimpleBool|CompoundBool|) : BoolExpr<_> -> Choice<unit, unit> =
    function
    | BVar _ | BTrue | BFalse -> SimpleBool
    | _ -> CompoundBool

/// Categorises expressions into simple or compound.
let (|SimpleExpr|CompoundExpr|) : Expr<_> -> Choice<unit, unit> =
    function
    | Bool (SimpleBool) -> SimpleExpr
    | Int (SimpleInt) -> SimpleExpr
    | _ -> CompoundExpr

/// <summary>
///     Tests for <c>Expr</c>.
/// </summary>
module Tests =
    open NUnit.Framework

    /// <summary>
    ///     NUnit tests for <c>Expr</c>.
    /// </summary>
    type NUnit () =
        /// Test cases for testing simple/compound arithmetic classification.
        static member IntSimpleCompound =
            [ TestCaseData(IInt 1L)
                .Returns(false)
                .SetName("Classify '1' as simple")
              TestCaseData(IAdd [IInt 1L; IInt 2L])
                .Returns(true)
                .SetName("Classify '1+2' as compound")
              TestCaseData(ISub [IAdd [IInt 1L; IInt 2L]; IInt 3L])
                .Returns(true)
                .SetName("Classify '(1+2)-3' as compound")
              TestCaseData(IVar "foo")
                .Returns(false)
                .SetName("Classify 'foo' as simple")
              TestCaseData(IMul [IVar "foo"; IVar "bar"])
                .Returns(true)
                .SetName("Classify 'foo * bar' as compound") ]

        /// Tests whether the simple/compound arithmetic patterns work correctly
        [<TestCaseSource("IntSimpleCompound")>]
        member x.``SimpleInt and CompoundInt classify properly`` e =
            match e with
            | SimpleInt -> false
            | CompoundInt -> true
