/// The part of the Z3 backend that translates terms to Z3.
module Starling.Z3.Translator

open Microsoft
open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Instantiate
open Starling.Sub
open Starling.Reifier
open Starling.Optimiser
open Starling.Errors.Z3.Translator

/// Converts a Starling arithmetic expression to a Z3 ArithExpr.
let rec arithToZ3 (ctx: Z3.Context) =
    function
    | AConst c -> c |> constToString |> ctx.MkIntConst :> Z3.ArithExpr
    | AInt i -> (i |> ctx.MkInt) :> Z3.ArithExpr
    | AAdd xs -> ctx.MkAdd (xs |> Seq.map (arithToZ3 ctx) |> Seq.toArray)
    | ASub xs -> ctx.MkSub (xs |> Seq.map (arithToZ3 ctx) |> Seq.toArray)
    | AMul xs -> ctx.MkMul (xs |> Seq.map (arithToZ3 ctx) |> Seq.toArray)
    | ADiv (x, y) -> ctx.MkDiv (arithToZ3 ctx x, arithToZ3 ctx y)

/// Converts a Starling Boolean expression to a Z3 ArithExpr.
and boolToZ3 (ctx : Z3.Context) =
    function
    | BConst c -> c |> constToString |> ctx.MkBoolConst
    | BTrue -> ctx.MkTrue ()
    | BFalse -> ctx.MkFalse ()
    | BAnd xs -> ctx.MkAnd (xs |> Seq.map (boolToZ3 ctx) |> Seq.toArray)
    | BOr xs -> ctx.MkOr (xs |> Seq.map (boolToZ3 ctx) |> Seq.toArray)
    | BImplies (x, y) -> ctx.MkImplies (boolToZ3 ctx x, boolToZ3 ctx y)
    | BEq (x, y) -> ctx.MkEq (exprToZ3 ctx x, exprToZ3 ctx y)
    | BGt (x, y) -> ctx.MkGt (arithToZ3 ctx x, arithToZ3 ctx y)
    | BGe (x, y) -> ctx.MkGe (arithToZ3 ctx x, arithToZ3 ctx y)
    | BLe (x, y) -> ctx.MkLe (arithToZ3 ctx x, arithToZ3 ctx y)
    | BLt (x, y) -> ctx.MkLt (arithToZ3 ctx x, arithToZ3 ctx y)
    | BNot x -> x |> boolToZ3 ctx |> ctx.MkNot

/// Converts a Starling expression to a Z3 Expr.
and exprToZ3 (ctx: Z3.Context) =
    function
    | BExpr b -> boolToZ3 ctx b :> Z3.Expr
    | AExpr a -> arithToZ3 ctx a :> Z3.Expr

/// Produces the reification of an unguarded func.
/// This corresponds to D^ in the theory.
let interpretVFunc ft func =
    instantiate func ft
    |> lift (withDefault BTrue)  // Undefined views go to True by metatheory
    |> mapMessages (curry InstantiationError func)

let interpretGFunc ft {Cond = c; Item = i} =
    interpretVFunc ft i
    |> lift (mkImplies c)

/// Interprets an entire view application over the given functable.
let interpretGView ft =
    Multiset.toSeq
    >> Seq.map (interpretGFunc ft)
    >> collect
    >> lift Seq.toList
    >> lift mkAnd

/// Interprets all of the views in a term over the given functable.
let interpretTerm ft : STerm<GView, VFunc> -> Result<FTerm, Error> =
    tryMapTerm ok (interpretGView ft) (interpretVFunc ft)

/// <summary>
///   Tries to make a <c>FuncTable</c> from <c>model</c>'s view definitions.
/// </summary>
/// <parameter name="model">
///   The model whose <c>ViewDefs</c> are to be turned into a <c>FuncTable</c>.
/// </parameter>
/// <returns>
///   A Chessie result, which, when ok, contains a <c>FuncTable</c> mapping
///   each defining view in <c>model</c> to its <c>BoolExpr</c> meaning.
/// <returns>
/// <remarks>
///   <para>
///     This stage requires all views in <c>model.ViewDefs</c> to be definite,
///     and will fail if any are not.
///   </para>
/// </remarks>
let makeFuncTable model =
    model.ViewDefs
    |> Seq.map
        (function
         | { View = vs; Def = None } -> IndefiniteConstraint vs |> fail
         | { View = vs; Def = Some s } -> (vs, s) |> ok)
    |> collect

/// <summary>
///   Interprets all views in a model, converting them to <c>FTerm</c>s.
/// </summary>
/// <parameter name="model">
///   The model whose views are to be interpreted.
/// </parameter>
/// <returns>
///   A Chessie result, which, when ok, contains a <c>Model</c> equivalent to
///   <c>model</c> except that each view is replaced with the <c>BoolExpr</c>
///   interpretation of it from <c>model</c>'s <c>ViewDefs</c>.
/// <returns>
/// <remarks>
///   <para>
///     This stage requires all views in <c>model.ViewDefs</c> to be definite,
///     and will fail if any are not.
///   </para>
/// </remarks>
let interpret model : Result<Model<FTerm, DFunc>, Error> =
    makeFuncTable model
    |> bind (fun ft -> tryMapAxioms (interpretTerm ft) model)

/// Combines the components of a reified term.
let combineTerm (ctx: Z3.Context) {Cmd = c; WPre = w; Goal = g} =
    (* This is effectively asking Z3 to refute (c ^ w => g).
     *
     * This arranges to:
     *   - ¬(c^w => g) premise
     *   - ¬(¬(c^w) v g) def. =>
     *   - ((c^w) ^ ¬g) deMorgan
     *   - (c^w^¬g) associativity.
     *)
    boolToZ3 ctx (mkAnd [c ; w; mkNot g] )

/// Combines reified terms into a list of Z3 terms.
let combineTerms ctx = mapAxioms (combineTerm ctx)
