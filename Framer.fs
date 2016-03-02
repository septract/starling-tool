/// The part of the Starling process that generates framed axioms.
module Starling.Framer

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Axiom

/// Instantiates a view parameter.
let instantiateParam fg (ty, name) = 
    frame fg name
    |> match ty with
       | Bool -> BConst >> BExpr
       | Int -> AConst >> AExpr

/// Instantiates a defining view into a view expression.
let instantiateFrame fg dvs = 
    dvs |> Multiset.map (fun { Name = n; Params = ps } -> 
               { Name = n
                 Params = List.map (instantiateParam fg) ps })

/// Converts an axiom into a list of framed axioms, by combining it with the
/// defining views of a model.
let frameAxiom ds fg (name, axiom) =
    // Each axiom comes in with a name like method_0,
    // where the 0 is the edge number.
    // This appends the viewdef number after the edge number.
    List.mapi
        (fun i { View = vs } -> 
              (sprintf "%s_%d" name i,
               { Axiom = axiom
                 Frame = instantiateFrame fg vs }))
         ds

/// Converts a model into a set of framed axioms.
let frameAxioms {ViewDefs = ds; Axioms = xs} =
    // We use a fresh variable generator to ensure every frame variable is unique.
    let fg = freshGen ()

    xs
    |> Map.toList
    |> concatMap (frameAxiom ds fg)
    |> Map.ofList

/// Converts a model into one over framed axioms.
let frame mdl = withAxioms (frameAxioms mdl) mdl
