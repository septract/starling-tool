/// Errors for the Horn and related modules of Starling.
module Starling.Errors.Horn

open Starling.Var
open Starling.Expr

/// An error caused when emitting a Horn clause.
type Error =
    /// A viewdef has a non-arithmetic param.
    | NonArithParam of Type * string
    /// The expression given is not supported in the given position.
    | UnsupportedExpr of Expr
    /// The expression given is compound, but empty.
    | EmptyCompoundExpr of exptype: string
