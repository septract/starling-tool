/// Convenience wrappers for Z3.
module Starling.Z3

open Microsoft

/// Makes an And out of a pair of two expressions.
let mkAnd2 (ctx: Z3.Context) (l, r) = ctx.MkAnd [| l; r |]
/// Makes an Or out of a pair of two expressions.
let mkOr2 (ctx: Z3.Context) (l, r) = ctx.MkOr [| l; r |]
/// Makes an Add out of a pair of two expressions.
let mkAdd2 (ctx: Z3.Context) (l, r) = ctx.MkAdd [| l; r |]
/// Makes a Sub out of a pair of two expressions.
let mkSub2 (ctx: Z3.Context) (l, r) = ctx.MkSub [| l; r |]
/// Makes a Mul out of a pair of two expressions.
let mkMul2 (ctx: Z3.Context) (l, r) = ctx.MkMul [| l; r |]


