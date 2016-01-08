/// Runs Z3 on the finished terms.
module Starling.Z3.Run

open Microsoft
open Starling.Model

/// Runs Z3 on a single term, given the context in `model`.
let runTerm (ctx: Z3.Context) term =
    let solver = ctx.MkSimpleSolver()
    solver.Assert [| term |]
    solver.Check [||]

/// Runs Z3 on a list of terms, given the context in `model`.
let run ctx = List.map (runTerm ctx)
