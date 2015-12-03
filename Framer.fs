/// The part of the Starling process that generates framed axioms.
module Starling.Framer

open Microsoft
open Starling.Var
open Starling.Model

/// Instantiates a view parameter.
let instantiateParam model (ty, name) =
    let ctx = model.Context
    ctx.MkFreshConst
        (name + "!frame!",
         match ty with
         | Int -> ctx.IntSort :> Z3.Sort
         | Bool -> ctx.BoolSort :> Z3.Sort)

/// Instantiates a defining view into a view expression.
let instantiateFrame model dvs =
    dvs
    |> List.map (fun dv -> {GCond = model.Context.MkTrue ()
                            GView = {VName = dv.VName
                                     VParams = List.map (instantiateParam model) dv.VParams}} )

/// Converts an axiom into a list of framed axioms, by combining it with the
/// defining views of a model.
let frameAxiom model axiom =
    List.map (fun dv -> {Axiom = axiom
                         Frame = instantiateFrame model dv.CViews})
             model.DefViews
    

/// Converts a model into a set of framed axioms.
let frame model =
    concatMap (frameAxiom model) model.Axioms
