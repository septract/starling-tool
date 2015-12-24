/// Runs Z3 on the finished terms.
module Starling.Z3.Run

open Starling.Model
open Microsoft.Z3

/// Runs Z3 on a single term, given the context in `model`.
let runTerm model term =
    let ctx = model.Context
    let solver = ctx.MkSimpleSolver()
    solver.Assert [| term |]
    solver.Check [||]

/// Runs Z3 on a list of terms, given the context in `model`.
let run model = List.map (runTerm model)