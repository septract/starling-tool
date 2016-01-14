module Starling.Flattener

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
    let p2 = inner.Conditions.Pre
    let p3 = inner.Conditions.Post
    let p4 = outer.Post
    
    // For do-while loops: [|P1|} id {|P2|}
    // For while loops: [|P1|} assume C {|P2|}
    let p1p2 = 
        { Conditions = 
              { Pre = p1
                Post = p2 }
          Inner = precom }
    
    // [|P3|] assume C [|P2|]
    let p3p2 = 
        { Conditions = 
              { Pre = p3
                Post = p2 }
          Inner = PrimAssume expr }
    
    // [|P3|] assume ¬C [|P4|]
    let p3p4 = 
        { Conditions = 
              { Pre = p3
                Post = p4 }
          Inner = PrimAssume(mkNot expr) }
    
    p1p2 :: p3p2 :: p3p4 :: flatAxioms model inner.Inner

/// Flattens an if-then-else loop into a list of flattened axioms.
and flatITE model expr outer inTrue inFalse = 
    (* While loops.
     * Translating [|P1|] if (C) { [|P2|] [|P3|] } else { [|P4|] [|P5|] } [|P6|].
     *)
    let p1 = outer.Pre
    let p2 = inTrue.Conditions.Pre
    let p3 = inTrue.Conditions.Post
    let p4 = inFalse.Conditions.Pre
    let p5 = inFalse.Conditions.Post
    let p6 = outer.Post
    
    // [|P1|} assume C {|P2|}
    let p1p2 = 
        { Conditions = 
              { Pre = p1
                Post = p2 }
          Inner = PrimAssume expr }
    
    // [|P3|] id [|P6|]
    let p3p6 = 
        { Conditions = 
              { Pre = p3
                Post = p6 }
          Inner = PrimId }
    
    // [|P1|] assume ~C [|P4|]
    let p1p4 = 
        { Conditions = 
              { Pre = p1
                Post = p4 }
          Inner = PrimAssume(mkNot expr) }
    
    // [|P5|] id [|P6|]
    let p5p6 = 
        { Conditions = 
              { Pre = p5
                Post = p6 }
          Inner = PrimId }
    
    let trues = p1p2 :: p3p6 :: flatAxioms model inTrue.Inner
    let falses = p1p4 :: p5p6 :: flatAxioms model inFalse.Inner
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

/// Flattens a model, changing its axioms from part axioms to flat axioms.
let flatten model = withAxioms (flatAxioms model model.Axioms) model
