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
    ///     A subtyped expression carrying an extended type record.
    /// </summary>
    /// <typeparam name="Sub">The type of the inner expression.</typeparam>
    /// <typeparam name="Rec">The type of the type record.</typeparam>
    type TypedSubExpr<'Sub, 'Rec> when 'Sub : equality =
        { /// <summary>The extended type record.</summary>
          SRec : 'Rec
          /// <summary>The expression itself.</summary>
          SExpr : 'Sub }
        override this.ToString() = sprintf "%A" this

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
        | IIdx of arr : TypedArrayExpr<'Var> * idx : IntExpr<'Var>
        | IInt of int64
        | IAdd of IntExpr<'Var> list
        | ISub of IntExpr<'Var> list
        | IMul of IntExpr<'Var> list
        | IDiv of IntExpr<'Var> * IntExpr<'Var>
        | IMod of IntExpr<'Var> * IntExpr<'Var>
        override this.ToString () = sprintf "%A" this

    /// <summary>
    ///     An integral expression carrying an extended type record.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and TypedIntExpr<'Var> when 'Var : equality =
        TypedSubExpr<IntExpr<'Var>, PrimTypeRec>

    /// <summary>
    ///     A Boolean expression.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and BoolExpr<'Var> when 'Var : equality =
        | BVar of 'Var
        | BIdx of arr : TypedArrayExpr<'Var> * idx : IntExpr<'Var>
        | BTrue
        | BFalse
        | BAnd of BoolExpr<'Var> list
        | BOr of BoolExpr<'Var> list
        | BImplies of BoolExpr<'Var> * BoolExpr<'Var>
        | BEq of Expr<'Var> * Expr<'Var>
        | BGt of TypedIntExpr<'Var> * TypedIntExpr<'Var>
        | BGe of TypedIntExpr<'Var> * TypedIntExpr<'Var>
        | BLe of TypedIntExpr<'Var> * TypedIntExpr<'Var>
        | BLt of TypedIntExpr<'Var> * TypedIntExpr<'Var>
        | BNot of BoolExpr<'Var>
        override this.ToString () = sprintf "%A" this

    /// <summary>
    ///     A Boolean expression carrying an extended type record.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and TypedBoolExpr<'Var> when 'Var : equality =
        TypedSubExpr<BoolExpr<'Var>, PrimTypeRec>

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
        | AIdx of arr : TypedArrayExpr<'Var> * idx : IntExpr<'Var>
        /// <summary>
        ///     A functional update of an array <c>arr</c> of type
        ///     <c>eltype[length]</c>, overriding index <c>idx</c> with value
        ///     <c>var</c>.
        /// </summary>
        | AUpd of arr : ArrayExpr<'Var>
                * idx : IntExpr<'Var>
                * nval : Expr<'Var>

    /// <summary>
    ///     An array expression carrying an extended type record.
    /// </summary>
    /// <typeparam name="Var">
    ///     The type of variables in the expression.
    /// </typeparam>
    and TypedArrayExpr<'Var> when 'Var : equality =
        TypedSubExpr<ArrayExpr<'Var>, ArrayTypeRec>

    /// Type for fresh variable generators.
    type FreshGen = bigint ref

/// <summary>
///     Creates a typed sub-expression.
/// </summary>
/// <param name="trec">The type record of the sub-expression.</param>
/// <param name="inner">The inner sub-expression to update.</param>
/// <typeparam name="Sub">The type of the new sub-expression.</typeparam>
/// <typeparam name="Sub">The inner record of the new sub-expression.</typeparam>
/// <returns>The resulting typed sub-expression.</returns>
let mkTypedSub (trec : 'Rec) (inner : 'Sub)
  : TypedSubExpr<'Sub, 'Rec> =
      { SRec = trec; SExpr = inner }

/// <summary>
///     Replaces the internals of a typed sub-expression with another
///     sub-expression.
/// </summary>
/// <param name="sub">The sub-expression to update.</param>
/// <param name="inner">The new inner sub-expression to add.</param>
/// <typeparam name="Sub">The type of the new sub-expression.</typeparam>
/// <typeparam name="Rec">The inner record of the sub-expression.</typeparam>
/// <returns>The resulting typed sub-expression.</returns>
let updateTypedSub (sub : TypedSubExpr<_, 'Rec>) (inner : 'Sub)
  : TypedSubExpr<'Sub, 'Rec> =
      mkTypedSub sub.SRec inner

/// <summary>
///     Maps a function over a typed sub-expression.
/// </summary>
/// <param name="f">The function to map over the sub-expression.</param>
/// <param name="sub">The sub-expression to update.</param>
/// <typeparam name="Sub">The type of the old sub-expression.</typeparam>
/// <typeparam name="Sub2">The type of the new sub-expression.</typeparam>
/// <typeparam name="Rec">The inner record of the sub-expression.</typeparam>
/// <returns>The resulting typed sub-expression.</returns>
let mapTypedSub (f : 'Sub -> 'Sub2) (sub : TypedSubExpr<'Sub, 'Rec>)
  : TypedSubExpr<'Sub2, 'Rec> =
    updateTypedSub sub (f sub.SExpr)

/// <summary>
///     Strips the extended type record of a typed sub-expression.
/// </summary>
/// <param name="sub">The sub-expression to strip.</param>
/// <typeparam name="Sub">The type of the sub-expression.</typeparam>
/// <returns>The inner sub-expression inside the typed container.</returns>
let stripTypeRec (sub : TypedSubExpr<'Sub, _>) : 'Sub =
    sub.SExpr

/// <summary>
///     Lifts an type-annotated sub-expression through a constructor.
/// </summary>
let liftTypedSub (f : ('Rec * 'Sub) -> 'T) (sub : TypedSubExpr<'Sub, 'Rec>) : 'T =
    // TODO(CaptainHayashi): proper doc comment.
    f (sub.SRec, sub.SExpr)

/// <summary>
///     The type record for a 'normal' expression.
/// </summary>
let normalRec : PrimTypeRec = { PrimSubtype = Normal }

/// <summary>
///     The type record for an indefinitely typed expression.
/// </summary>
let indefRec : PrimTypeRec = { PrimSubtype = Indef }

/// <summary>
///     Converts a TypedBoolExpr to a Type.
/// </summary>
let typedBoolToType (bsub : TypedBoolExpr<'Var>) : Type =
    // TODO(CaptainHayashi): proper doc comment.
    Type.Bool (bsub.SRec, ())

/// <summary>
///     Converts a TypedBoolExpr to an Expr.
/// </summary>
let typedBoolToExpr (bsub : TypedBoolExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    liftTypedSub Expr.Bool bsub

/// <summary>
///     Converts a BoolExpr to a TypedBoolExpr using the normal type.
/// </summary>
let normalBool (bool : BoolExpr<'Var>) : TypedBoolExpr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    mkTypedSub normalRec bool

/// <summary>
///     Converts a BoolExpr to a TypedBoolExpr using the indefinite type.
/// </summary>
let indefBool (bool : BoolExpr<'Var>) : TypedBoolExpr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    mkTypedSub indefRec bool

/// <summary>
///     Converts a BoolExpr to an Expr using the normal type.
/// </summary>
let normalBoolExpr (bool : BoolExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    typedBoolToExpr (normalBool bool)

/// <summary>
///     Converts a BoolExpr to an Expr using the indefinite type.
/// </summary>
let indefBoolExpr (bool : BoolExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    typedBoolToExpr (indefBool bool)

/// <summary>
///     Constructs a Boolean typed variable from a variable using the normal type.
/// </summary>
let normalBoolVar (var : 'Var) : CTyped<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    Bool (normalRec,  var)

/// <summary>
///     Constructs a Boolean typed variable from a variable using the indefinite type.
/// </summary>
let indefBoolVar (var : 'Var) : CTyped<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    Bool (indefRec, var)

/// <summary>
///     Converts a TypedIntExpr to a Type.
/// </summary>
let typedIntToType (bsub : TypedIntExpr<'Var>) : Type =
    // TODO(CaptainHayashi): proper doc comment.
    Type.Int (bsub.SRec, ())

/// <summary>
///     Converts a TypedIntExpr to an Expr.
/// </summary>
let typedIntToExpr (bsub : TypedIntExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    liftTypedSub Expr.Int bsub

/// <summary>
///     Converts an IntExpr to a TypedIntExpr using the normal type.
/// </summary>
let normalInt (int : IntExpr<'Var>) : TypedIntExpr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    mkTypedSub normalRec int

/// <summary>
///     Converts an IntExpr to a TypedIntExpr using the indefinite type.
/// </summary>
let indefInt (int : IntExpr<'Var>) : TypedIntExpr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    mkTypedSub indefRec int

/// <summary>
///     Constructs an integer typed variable from a variable using the normal type.
/// </summary>
let normalIntVar (var : 'Var) : CTyped<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    Int (normalRec, var)

/// <summary>
///     Constructs an integer typed variable from a variable using the indefinite type.
/// </summary>
let indefIntVar (var : 'Var) : CTyped<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    Int (indefRec, var)

/// <summary>
///     Converts an IntExpr to an Expr using the normal type.
/// </summary>
let normalIntExpr (int : IntExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    typedIntToExpr (normalInt int)

/// <summary>
///     Converts an IntExpr to an Expr using the indefinite type.
/// </summary>
let indefIntExpr (int : IntExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    typedIntToExpr (indefInt int)

/// <summary>
///     Constructs an array type record.
/// </summary>
/// <param name="eltype">The inner element type.</param>
/// <param name="length">The optional length.</param>
/// <returns>The corresponding array type record.</returns>
let mkArrayTypeRec (eltype : Type) (length : int option) : ArrayTypeRec =
    { ElementType = eltype; Length = length }

/// <summary>
///     Constructs an array type.
/// </summary>
/// <param name="eltype">The inner element type.</param>
/// <param name="length">The optional length.</param>
/// <returns>The corresponding array type.</returns>
let mkArrayType (eltype : Type) (length : int option) : Type =
    Array (mkArrayTypeRec eltype length, ())

/// <summary>
///     Constructs an typed array expression.
/// </summary>
/// <param name="eltype">The inner element type.</param>
/// <param name="length">The optional length.</param>
/// <param name="inner">The inner array expression.</param>
/// <typeparam name="Var">Type of variables inside the expression.</typeparam>
/// <returns>The corresponding array type record.</returns>
let mkTypedArrayExpr (eltype : Type) (length : int option) (inner : ArrayExpr<'Var>)
  : TypedArrayExpr<'Var> =
    mkTypedSub (mkArrayTypeRec eltype length) inner

/// <summary>
///     Converts a TypedArrayExpr to an Expr.
/// </summary>
let typedArrayToExpr (bsub : TypedArrayExpr<'Var>) : Expr<'Var> =
    // TODO(CaptainHayashi): proper doc comment.
    liftTypedSub Expr.Array bsub


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
    and printIntExpr (pVar : 'Var -> Doc) (int : IntExpr<'Var>) : Doc =
        match int with
        | IVar c -> pVar c
        | IInt i -> i |> sprintf "%i" |> String
        | IIdx (arr, idx) -> printIdx pVar (stripTypeRec arr) idx
        | IAdd xs -> sexpr "+" (printIntExpr pVar) xs
        | ISub xs -> sexpr "-" (printIntExpr pVar) xs
        | IMul xs -> sexpr "*" (printIntExpr pVar) xs
        | IDiv (x, y) -> sexpr "/" (printIntExpr pVar) [x; y]
        | IMod (x, y) -> sexpr "%" (printIntExpr pVar) [x; y]

    /// Pretty-prints a Boolean expression.
    and printBoolExpr (pVar : 'Var -> Doc) (bool : BoolExpr<'Var>) : Doc =
        match bool with
        | BVar c -> pVar c
        | BIdx (arr, idx) -> printIdx pVar (stripTypeRec arr) idx
        | BTrue -> String "true"
        | BFalse -> String "false"
        | BAnd xs -> svexpr "and" (printBoolExpr pVar) xs
        | BOr xs -> svexpr "or" (printBoolExpr pVar) xs
        | BImplies (x, y) -> svexpr "=>" (printBoolExpr pVar) [x; y]
        | BEq (x, y) -> sexpr "=" (printExpr pVar) [x; y]
        | BGt (x, y) -> sexpr ">" (stripTypeRec >> printIntExpr pVar) [x; y]
        | BGe (x, y) -> sexpr ">=" (stripTypeRec >> printIntExpr pVar) [x; y]
        | BLe (x, y) -> sexpr "<=" (stripTypeRec >> printIntExpr pVar) [x; y]
        | BLt (x, y) -> sexpr "<" (stripTypeRec >> printIntExpr pVar) [x; y]
        | BNot x -> sexpr "not" (printBoolExpr pVar) [x]

    /// Pretty-prints an array expression.
    and printArrayExpr (pVar : 'Var -> Doc) (arr : ArrayExpr<'Var>) : Doc =
        match arr with
        | AVar c -> pVar c
        | AIdx (arr, idx) -> printIdx pVar (stripTypeRec arr) idx
        | AUpd (arr, idx, value) ->
            cmdSexpr "store"
                [ printIntExpr pVar idx
                  printExpr pVar value
                  printArrayExpr pVar arr ]

    /// Pretty-prints an expression.
    and printExpr (pVar : 'Var -> Doc) : Expr<'Var> -> Doc =
        function
        | Int (_, i) -> printIntExpr pVar i
        | Bool (_, b) -> printBoolExpr pVar b
        | Array (_, a) -> printArrayExpr pVar a


/// Partial pattern that matches a Boolean equality on arithmetic expressions.
let (|BIEq|_|) (bool : BoolExpr<'var>)
  : (IntExpr<'var> * IntExpr<'var>) option =
    match bool with
    | BEq (Int (_, x), Int (_, y)) -> Some (x, y)
    | _ -> None

/// Partial pattern that matches a Boolean equality on arithmetic expressions.
/// and preserves the extended type record.
let (|TBIEq|_|) (bool : BoolExpr<'var>)
  : (TypedIntExpr<'var> * TypedIntExpr<'var>) option =
    match bool with
    | BEq (Int (xr, x), Int (yr, y)) -> Some (mkTypedSub xr x, mkTypedSub yr y)
    | _ -> None


/// Partial pattern that matches a Boolean equality on Boolean expressions.
let (|BBEq|_|) (bool : BoolExpr<'var>)
  : (BoolExpr<'var> * BoolExpr<'var>) option =
    match bool with
    | BEq (Bool (_, x), Bool (_, y)) -> Some (x, y)
    | _ -> None

/// Partial pattern that matches a Boolean equality on Boolean expressions
/// and preserves the extended type record.
let (|TBBEq|_|) (bool : BoolExpr<'var>)
  : (TypedBoolExpr<'var> * TypedBoolExpr<'var>) option =
    match bool with
    | BEq (Bool (xr, x), Bool (yr, y)) -> Some (mkTypedSub xr x, mkTypedSub yr y)
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

/// <summary>
///     Unfolds all top-level conjunctions in a Boolean expression,
///     returning a list of all conjoined expressions.
/// </summary>
/// <param name="expr">The Boolean expression to unfold.</param>
/// <typeparam name="Var">Type of variables in the expression.</typeparam>
/// <returns>
///     The list of all Boolean expressions reachable from
///     <paramref name="expr"/> by walking through top-level
///     conjunctions.
/// </returns>
let rec unfoldAnds (expr : BoolExpr<'Var>) : BoolExpr<'Var> list =
    match expr with
    | BAnd xs -> concatMap unfoldAnds xs
    | x -> [x]

/// <summary>
///     Collects all of the ints in a list of integer expressions, folds
///     them together with a given operator and unit, and returns them
///     separately from the rest of the expression.
/// </summary>
let sepInts (f : int64 -> int64 -> int64) (u: int64) (e : IntExpr<'var> list)
  : int64 * IntExpr<'var> list =
    let accum acc x =
        match x with
        | IInt k -> (f acc k, None  )
        | _      -> (acc    , Some x)

    let intBit, restMaybe = mapAccumL accum u e
    let rest = List.choose id restMaybe
    (intBit, rest)

/// <summary>
///     Collects all of the ints in a list of integer expressions, folds
///     them together with a given operator and unit, and appends the result if
///     it is not the unit.
/// </summary>
let foldInts (f : int64 -> int64 -> int64) (u: int64) (e : IntExpr<'var> list) =
    let intBit, rest = sepInts f u e
    // Shuffling to back is inefficient but gives more natural expressions.
    if intBit = u then rest else (rest @ [IInt intBit])


/// Curried wrapper over BGt.
let mkGt (a : TypedIntExpr<'var>) (b : TypedIntExpr<'var>) : BoolExpr<'var> =
    match (stripTypeRec a, stripTypeRec b) with
    | IInt x, IInt y when x >  y -> BTrue
    | IInt x, IInt y when x <= y -> BFalse
    | IVar x, IVar y when x =  y -> BFalse
    // x + k > z <-> c > x - k
    | IAdd xs, IInt y ->
        let yk, xs' = sepInts (+) 0L xs
        BGt (updateTypedSub a (IAdd xs'), updateTypedSub b (IInt (y - yk)))
    // x - k > z <-> c > x + k
    // TODO(MattWindsor91): generalise this?
    | ISub [ x; IInt k ], IInt y ->
        BGt (updateTypedSub a x, updateTypedSub b (IInt (y + k)))
    | _ -> BGt (a, b)
/// As mkGt, but uses the 'int' subtype.
let mkIntGt (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    mkGt (mkTypedSub normalRec a) (mkTypedSub normalRec b)
/// Curried wrapper over BGe.
let mkGe (a : TypedIntExpr<'var>) (b : TypedIntExpr<'var>) : BoolExpr<'var> =
    match (stripTypeRec a, stripTypeRec b) with
    | IInt x, IInt y when x >= y -> BTrue
    | IInt x, IInt y when x <  y -> BFalse
    | IVar x, IVar y when x =  y -> BTrue
    // x + k >= z <-> c >= x - k
    | IAdd xs, IInt y ->
        let yk, xs' = sepInts (+) 0L xs
        BGe (updateTypedSub a (IAdd xs'), updateTypedSub b (IInt (y - yk)))
    // x - k >= z <-> c >= x + k
    // TODO(MattWindsor91): generalise this?
    | ISub [ x; IInt k ], IInt y ->
        BGe (updateTypedSub a x, updateTypedSub b (IInt (y + k)))
    | _ -> BGe (a, b)
/// As mkGe, but uses the 'int' subtype.
let mkIntGe (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    mkGe (mkTypedSub normalRec a) (mkTypedSub normalRec b)
/// Curried wrapper over BLt.
let mkLt (a : TypedIntExpr<'var>) (b : TypedIntExpr<'var>) : BoolExpr<'var> =
    match (stripTypeRec a, stripTypeRec b) with
    | IInt x, IInt y when x <  y -> BTrue
    | IInt x, IInt y when x >= y -> BFalse
    | IVar x, IVar y when x =  y -> BFalse
    // x + k < z <-> c < x - k
    | IAdd xs, IInt y ->
        let yk, xs' = sepInts (+) 0L xs
        BLt (updateTypedSub a (IAdd xs'), updateTypedSub b (IInt (y - yk)))
    // x - k < z <-> c < x + k
    // TODO(MattWindsor91): generalise this?
    | ISub [ x; IInt k ], IInt y ->
        BLt (updateTypedSub a x, updateTypedSub b (IInt (y + k)))
    | _ -> BLt (a, b)
/// As mkLt, but uses the 'int' subtype.
let mkIntLt (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    mkLt (mkTypedSub normalRec a) (mkTypedSub normalRec b)
/// Curried wrapper over BLe.
let mkLe (a : TypedIntExpr<'var>) (b : TypedIntExpr<'var>) : BoolExpr<'var> =
    match (stripTypeRec a, stripTypeRec b) with
    | IInt x, IInt y when x <= y -> BTrue
    | IInt x, IInt y when x >  y -> BFalse
    | IVar x, IVar y when x =  y -> BTrue
    // x + k <= z <-> c <= x - k
    | IAdd xs, IInt y ->
        let yk, xs' = sepInts (+) 0L xs
        BLe (updateTypedSub a (IAdd xs'), updateTypedSub b (IInt (y - yk)))
    // x - k <= z <-> c <= x + k
    // TODO(MattWindsor91): generalise this?
    | ISub [ x; IInt k ], IInt y ->
        BLe (updateTypedSub a x, updateTypedSub b (IInt (y + k)))
    | _ -> BLe (a, b)
/// As mkLe, but uses the 'int' subtype.
let mkIntLe (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    mkLe (mkTypedSub normalRec a) (mkTypedSub normalRec b)

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
    // Use the integer simplifiers for inequalities.
    | BGt (x, y) -> mkGt x y
    | BGe (x, y) -> mkGe x y
    | BLe (x, y) -> mkLe x y
    | BLt (x, y) -> mkLt x y
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
    // We can recursively simplify equality providing it's between two 'bool's.
    // A Boolean equality between two contradictions or tautologies is always true.
    | TBBEq ({ SRec = xr; SExpr = x }, { SRec = yr; SExpr = y })
        when unifyPrimTypeRecs [ normalRec; xr; yr ] <> None ->
        match simp x, simp y with
        | BFalse, BFalse
        | BTrue, BTrue      -> BTrue
        | BTrue, BFalse
        | BFalse, BTrue     -> BFalse
        | x, BTrue          -> x
        | BTrue, x          -> x
        | x, BFalse         -> simp (BNot x)
        | BFalse, x         -> simp (BNot x)
        | x, y              -> BEq(Bool (xr, x), Bool (yr, y))
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
    | CTyped.Int (t, i) -> Expr.Int (t, IVar i)
    | CTyped.Bool (t, b) -> Expr.Bool (t, BVar b)
    | CTyped.Array (t, a) -> Expr.Array (t, AVar a)

/// Converts a VarMap to a sequence of expressions.
let varMapToExprs
  (marker : string -> 'markedvar)
  : Map<string, Type> -> Expr<'markedvar> seq =
    Map.toSeq >> Seq.map (fun (name, ty) -> name |> withType ty |> mapCTyped marker |> mkVarExp)

(* The following are just curried versions of the usual constructors. *)

// TODO(CaptainHayashi): move these optimisations into an integer simplification
// function and hook it up to simp.

/// Curried wrapper over BEq.
let mkEq (a : Expr<'var>) (b : Expr<'var>) : BoolExpr<'var> = BEq (a, b)

/// Makes an arithmetic equality with a plain Int type.
let iEq (a : IntExpr<'var>) (b : IntExpr<'var>) : BoolExpr<'var> =
    BEq (Int (normalRec, a), Int (normalRec, b))

/// Makes a Boolean equality with a plain Boolean type.
let bEq (a : BoolExpr<'var>) (b : BoolExpr<'var>) : BoolExpr<'var> =
    BEq (Bool (normalRec, a), Bool (normalRec, b))

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
let mkImplies (a : BoolExpr<'var>) (b : BoolExpr<'var>) : BoolExpr<'var> =
    simp (BImplies(a, b))

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

/// Makes a Sub out of a pair of two expressions.
let rec mkSub2 (l : IntExpr<'var>) (r : IntExpr<'var>) : IntExpr<'var> =
    match (l, r) with
    | (IInt x , IInt y)  -> IInt (x - y)
    | (x      , IInt 0L) -> x
    | (x      , IInt k ) when k < 0L -> mkAdd2 x (IInt k)
    | (ISub xs, x      ) -> ISub (xs @ [ x ])
    | _                  -> ISub [ l; r ]
/// Makes an Add out of a pair of two expressions.
and mkAdd2 (l : IntExpr<'var>) (r : IntExpr<'var>) : IntExpr<'var> =
    match (l, r) with
    | (IInt 0L, x) | (x, IInt 0L)   -> x
    | (IInt x, IInt y)              -> IInt (x + y)
    | (IAdd xs, IAdd ys)            -> IAdd (foldInts (+) 0L (xs @ ys))
    | (IAdd xs, y) | (y, IAdd xs)   -> IAdd (foldInts (+) 0L (y :: xs))
    // Try to move common subtractions outside the addition
    // TODO(MattWindsor91): this could do with being generalised.

    // (x + (y - k)) -> ((x + y) - k)
    | (x, (ISub [ y; IInt k ]))     -> mkSub2 (mkAdd2 x y) (IInt k)
    // ((x - k) + l) -> (x - (k-l)) but only when k, l are integers
    | (ISub [ x ; IInt k ], IInt l) -> mkSub2 x (IInt (k - l))
    | _                             -> IAdd (foldInts (+) 0L [ l; r ])

/// Makes an increment expression.
let mkInc (x : IntExpr<'Var>) : IntExpr<'Var> = mkAdd2 x (IInt 1L)

/// Makes a variable increment expression.
let incVar (x : 'Var) : IntExpr<'Var> = mkInc (IVar x)

/// Makes a decrement expression.
let mkDec (x : IntExpr<'Var>) : IntExpr<'Var> = mkSub2 x (IInt 1L)


/// Makes an Add out of a sequence of expressions.
let mkAdd (xs : IntExpr<'var> seq) : IntExpr<'var> =
    // TODO(CaptainHayashi): produce a trimmed list, instead of mkAdd2ing.
    Seq.fold mkAdd2 (IInt 0L) xs

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
    | Bool (_, SimpleBool) -> SimpleExpr
    | Int (_, SimpleInt) -> SimpleExpr
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
