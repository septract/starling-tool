/// The part of the Starling process that generates framed axioms.
module Starling.Framer

open Microsoft
open Starling.Collections
open Starling.Var
open Starling.Model

/// Converts a Starling type to a Z3 sort.
let typeToSort (ctx : Z3.Context) = 
    function 
    | Type.Int -> ctx.IntSort :> Z3.Sort
    | Type.Bool -> ctx.BoolSort :> Z3.Sort

/// Instantiates a view parameter.
let instantiateParam model (ty, name) = 
    let ctx = model.Context
    ctx.MkFreshConst(name + "!frame", typeToSort ctx ty)

/// Instantiates a defining view into a view expression.
let instantiateFrame model dvs = 
    dvs |> Multiset.map (fun { Name = n; Params = ps } -> 
               { Cond = model.Context.MkTrue()
                 Item = 
                     { Name = n
                       Params = List.map (instantiateParam model) ps } })

/// Converts an axiom into a list of framed axioms, by combining it with the
/// defining views of a model.
let frameAxiom model axiom = 
    List.map (fun { CViews = vs } -> 
        { Axiom = axiom
          Frame = instantiateFrame model vs }) model.DefViews

/// Converts a model into a set of framed axioms.
let frame model = concatMap (frameAxiom model) model.Axioms
