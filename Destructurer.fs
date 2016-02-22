module Starling.Destructurer

open Starling.Collections
open Starling.Expr
open Starling.Sub
open Starling.Model

/// Flattens a [do-]while loop into a list of flat axioms.
/// The difference between the two loops is expressed by the command inside
/// precom.
let rec flatWhile model expr outerPre outerPost inner isDo = 
    (* If isDo:
     *   Translating [|P1|] do { [|P2|] [|P3|] } while (C) [|P4|].
     * Else:
     *   Translating [|P1|] while (C) { [|P2|] [|P3|] } [|P4|].
     *)
    let p1 = outerPre
    let p2 = inner.Pre
    let p3 = inner.Post
    let p4 = outerPost
    
    let id = func "Id" []
    let assumeC = func "Assume" [expr |> BExpr |> before]
    let assumeNotC = func "Assume" [expr |> mkNot |> BExpr |> before]
    
    // For do-while loops: [|P1|} id [|P2|]
    // For while loops: [|P1|] assume C [|P2|]
    let p1p2 = axiom p1 (if isDo then id else assumeC) p2
    
    // [|P3|] assume C [|P2|]
    let p3p2 = axiom p3 assumeC p2
    
    // [|P3|] assume ¬C [|P4|]
    let p3p4 = axiom p3 assumeNotC p4

    let inPath = p1p2 :: p3p2 :: p3p4 :: flatAxioms model inner.Cmd

    // For while loops, add path [|P1|] assume ¬C [|P4|] (not entering loop).
    if isDo
    then inPath
    else (axiom p1 assumeNotC p4) :: inPath

/// Flattens an if-then-else loop into a list of flattened axioms.
and flatITE model expr outerPre outerPost inTrue inFalse = 
    (* While loops.
     * Translating [|P1|] if (C) { [|P2|] [|P3|] } else { [|P4|] [|P5|] } [|P6|].
     *)
    let p1 = outerPre
    let p2 = inTrue.Pre
    let p3 = inTrue.Post
    let p4 = inFalse.Pre
    let p5 = inFalse.Post
    let p6 = outerPost
    
    // [|P1|} assume C {|P2|}
    let p1p2 = axiom p1 (func "Assume" [expr |> BExpr |> before]) p2
    
    // [|P3|] id [|P6|]
    let p3p6 = axiom p3 (func "Id" []) p6
    
    // [|P1|] assume ~C [|P4|]
    let p1p4 = axiom p1 (func "Assume" [expr |> mkNot |> BExpr |> before]) p4
    
    // [|P5|] id [|P6|]
    let p5p6 = axiom p5 (func "Id" []) p6
    
    let trues = p1p2 :: p3p6 :: flatAxioms model inTrue.Cmd
    let falses = p1p4 :: p5p6 :: flatAxioms model inFalse.Cmd
    List.concat [ trues; falses ]

/// Flattens a part axiom into a list of flattened axioms.
and flatAxiom model { Pre = pre; Post = post; Cmd = cmd } = 
    match cmd with
    | Prim p -> [axiom pre p post]
    | While(isDo, expr, inner) -> 
        flatWhile model expr pre post inner isDo
    | ITE(expr, inTrue, inFalse) -> flatITE model expr pre post inTrue inFalse

/// Flattens a list of part axioms into a list of flattened axioms.
and flatAxioms model = concatMap (flatAxiom model)

/// Flattens a model's axioms, removing control-flow structure.
let destructure model = withAxioms (flatAxioms model model.Axioms) model
