/// Convenience wrappers for Z3.
[<AutoOpen>]
module Starling.Z3.Utils

open Microsoft
open Starling.Model

// A Z3-reified term.
type ZTerm = Term<Z3.BoolExpr, Z3.BoolExpr, Z3.BoolExpr>
