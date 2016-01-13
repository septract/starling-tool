/// The part of the Starling process that generates framed axioms.
module Starling.Framer

open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Model

/// Instantiates a view parameter.
let instantiateParam fg (ty, name) = 
    frame fg name
    |> match ty with
       | Bool -> BConst >> BExpr
       | Int -> AConst >> AExpr

/// Instantiates a defining view into a view expression.
let instantiateFrame fg dvs = 
    dvs |> Multiset.map (fun { Name = n; Params = ps } -> 
               { Cond = BTrue
                 Item = 
                     { Name = n
                       Params = List.map (instantiateParam fg) ps } })

/// Converts an axiom into a list of framed axioms, by combining it with the
/// defining views of a model.
let frameAxiom ds fg axiom = 
    List.map (fun { CViews = vs } -> 
        { Axiom = axiom
          Frame = instantiateFrame fg vs }) ds

/// Converts a model into a set of framed axioms.
let frameAxioms {DefViews = ds; Axioms = xs} =
    // We use a fresh variable generator to ensure every frame variable is unique.
    concatMap (frameAxiom ds (freshGen ())) xs

/// Converts a model into one over framed axioms.
let frame mdl = withAxioms (frameAxioms mdl) mdl
