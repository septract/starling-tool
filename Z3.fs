/// Convenience wrappers for Z3.
module Starling.Z3

open Microsoft

/// Active pattern for matching on true, false, and undefined.
/// This pattern is sound but likely not complete.
let (|ZTrue|ZFalse|ZUndef|) (z: Z3.BoolExpr) =
    match z.BoolValue with
    | Z3.Z3_lbool.Z3_L_TRUE -> ZTrue
    | Z3.Z3_lbool.Z3_L_FALSE -> ZFalse
    | _ -> ZUndef

(*
 * Expression constructors
 *)

/// Shortened version of making an ArithExpr from an integer constant.
let mkAInt (ctx: Z3.Context) (k: int) = ctx.MkInt k :> Z3.ArithExpr

/// Slightly optimised version of ctx.MkAnd.
/// Returns true for the empty array, and x for the singleton set {x}.
let mkAnd (ctx: Z3.Context) (conjuncts: Z3.BoolExpr seq) =
    if Seq.exists (fun (x: Z3.BoolExpr) -> x.IsFalse) conjuncts
    then ctx.MkFalse ()
    else
        let cs = conjuncts |> Seq.filter (fun (x: Z3.BoolExpr) -> not x.IsTrue) |> Array.ofSeq
        match cs with
        // True is the zero of and.
        | [||] -> ctx.MkTrue ()
        | [| x |] -> x
        | xs -> ctx.MkAnd (xs)

/// Slightly optimised version of ctx.MkOr.
/// Returns false for the empty set, and x for the singleton set {x}.
let mkOr (ctx: Z3.Context) (disjuncts: Z3.BoolExpr seq) =
    if Seq.exists (fun (x: Z3.BoolExpr) -> x.IsTrue) disjuncts
    then ctx.MkTrue ()
    else
        let ds = disjuncts |> Seq.filter (fun (x: Z3.BoolExpr) -> not x.IsFalse) |> Array.ofSeq
        match ds with
        // False is the zero of or.
        | [||] -> ctx.MkFalse ()
        | [| x |] -> x
        | xs -> ctx.MkOr (xs)

/// Makes an And from a pair of two expressions.
let mkAnd2 (ctx: Z3.Context) l r = mkAnd ctx [l ; r]

/// Makes an Or from a pair of two expressions.
let mkOr2 (ctx: Z3.Context) l r = mkOr ctx [l ; r]

/// Makes not-equals.
let mkNeq (ctx: Z3.Context) l r =
    ctx.MkNot (ctx.MkEq (l, r))

let mkNot (ctx: Z3.Context) x =
    match x with
    // Simplify obviously false or true exprs to their negation.
    | ZFalse -> ctx.MkTrue ()
    | ZTrue -> ctx.MkFalse ()
    | _ -> ctx.MkNot x

/// Makes an implication from a pair of two expressions.
let mkImplies (ctx: Z3.Context) l r =
    (* l => r <-> ¬l v r.
     * This implies (excuse the pun) that l false or r true will
     * make the expression a tautology;
     * similarly, l true yields r, and r false yields ¬l.
     *)
    match l, r with
    | (ZFalse, _) | (_, ZTrue) -> ctx.MkTrue ()
    | (x, ZFalse) -> mkNot ctx x
    | (ZTrue, x) -> x
    | _ -> ctx.MkImplies (l, r)

/// Makes an Add out of a pair of two expressions.
let mkAdd2 (ctx: Z3.Context) l r = ctx.MkAdd [| l; r |]
/// Makes a Sub out of a pair of two expressions.
let mkSub2 (ctx: Z3.Context) l r = ctx.MkSub [| l; r |]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 (ctx: Z3.Context) l r = ctx.MkMul [| l; r |]

(* The following are just curried versions of the usual MkXYZ. *)

/// Curried wrapper over MkGt.
let mkGt (ctx: Z3.Context) = curry ctx.MkGt
/// Curried wrapper over MkGe.
let mkGe (ctx: Z3.Context) = curry ctx.MkGe
/// Curried wrapper over MkLt.
let mkLt (ctx: Z3.Context) = curry ctx.MkLt
/// Curried wrapper over MkLe.
let mkLe (ctx: Z3.Context) = curry ctx.MkLe
/// Curried wrapper over MkEq.
let mkEq (ctx: Z3.Context) = curry ctx.MkEq
/// Curried wrapper over MkDiv.
let mkDiv (ctx: Z3.Context) = curry ctx.MkDiv
