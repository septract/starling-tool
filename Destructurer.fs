module Starling.Destructurer

open Starling.Expr
open Starling.Model

/// Flattens a [do-]while loop into a list of flat axioms.
/// The difference between the two loops is expressed by the command inside
/// precom.
let rec flatWhile model expr outer inner precom = 
    (* While and do-while loops.
     * Translating [|P1|] do { [|P2|] [|P3|] } while (C) [|P4|].
     *)
    let p1 = outer.Pre
    let p2 = inner.Conds.Pre
    let p3 = inner.Conds.Post
    let p4 = outer.Post
    
    // For do-while loops: [|P1|} id {|P2|}
    // For while loops: [|P1|} assume C {|P2|}
    let p1p2 = axiom p1 precom p2
    
    // [|P3|] assume C [|P2|]
    let p3p2 = axiom p3 (PrimAssume expr) p2
    
    // [|P3|] assume ¬C [|P4|]
    let p3p4 = axiom p3 (PrimAssume(mkNot expr)) p4
    
    p1p2 :: p3p2 :: p3p4 :: flatAxioms model inner.Cmd

/// Flattens an if-then-else loop into a list of flattened axioms.
and flatITE model expr outer inTrue inFalse = 
    (* While loops.
     * Translating [|P1|] if (C) { [|P2|] [|P3|] } else { [|P4|] [|P5|] } [|P6|].
     *)
    let p1 = outer.Pre
    let p2 = inTrue.Conds.Pre
    let p3 = inTrue.Conds.Post
    let p4 = inFalse.Conds.Pre
    let p5 = inFalse.Conds.Post
    let p6 = outer.Post
    
    // [|P1|} assume C {|P2|}
    let p1p2 = axiom p1 (PrimAssume expr) p2
    
    // [|P3|] id [|P6|]
    let p3p6 = axiom p3 PrimId p6
    
    // [|P1|] assume ~C [|P4|]
    let p1p4 = axiom p1 (PrimAssume(mkNot expr)) p4
    
    // [|P5|] id [|P6|]
    let p5p6 = axiom p5 PrimId p6
    
    let trues = p1p2 :: p3p6 :: flatAxioms model inTrue.Cmd
    let falses = p1p4 :: p5p6 :: flatAxioms model inFalse.Cmd
    List.concat [ trues; falses ]

/// Flattens a part axiom into a list of flattened axioms.
and flatAxiom model = 
    function 
    | PAAxiom ax -> [ ax ] // These are already flat axioms.
    | PAWhile(isDo, expr, outer, inner) -> 
        flatWhile model expr outer inner (if isDo then PrimId
                                          else PrimAssume expr)
    | PAITE(expr, outer, inTrue, inFalse) -> flatITE model expr outer inTrue inFalse

/// Flattens a list of part axioms into a list of flattened axioms.
and flatAxioms model = concatMap (flatAxiom model)

/// Flattens a model's axioms, removing control-flow structure.
let destructure model = withAxioms (flatAxioms model model.Axioms) model
