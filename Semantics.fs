/// <summary>
///   Module containing the semantic instantiator.
///
///   <para>
///     The semantic instantiator converts the commands in a model's
///     axioms into Boolean expressions, by instantiating them in
///     accordance with the model's semantic definitions.
///   </para>
///   <para>
///     It also ensures variables not mentioned in a command's semantic
///     definition are preserved in the resulting expression.
///   </para>
/// </summary>
module Starling.Semantics

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Sub
open Starling.Instantiate

/// Type of errors relating to semantics instantiation.
type Error =
    /// There was an error instantiating a semantic definition.
    | Instantiate of cmd: VFunc * error: Instantiate.Error
    /// A command has a missing semantic definition.
    | MissingDef of cmd: VFunc

/// Generates a framing relation for a given variable.
let frameVar name ty =
    let ve = mkVarExp(ty, name)
    
    BEq(subExpr (liftMarker After always) ve,
        subExpr (liftMarker Before always) ve)

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame model expr = 
    // Find all the bound post-variables in the expression...
    let evars =
        expr
        |> varsInBool
        |> Seq.choose (function | After x -> Some x
                                | _ -> None)
        |> Set.ofSeq

    // Then, for all of the variables in the model, choose those not in evars, and make frame expressions for them.
    Seq.append (Map.toSeq model.Globals) (Map.toSeq model.Locals)
    // TODO(CaptainHayashi): this is fairly inefficient.
    |> Seq.filter (fun (name, _) -> not (Set.contains name evars))
    |> Seq.map (uncurry frameVar)

/// Translate a Prim to an expression completely characterising it.
/// This is the combination of the Prim's action (via emitPrim) and
/// a set of framing terms forcing unbound variables to remain constant
/// (through frame).
let semanticsOf model prim =
    (* First, instantiate according to the semantics. 
     * This can succeed but return None.  This means there is no
     * entry (erroneous or otherwise) in the semantics for this prim.
     * Since this is an error in this case, make it one.
     *)
    let actions =
        instantiate prim model.Semantics
        |> mapMessages (curry Instantiate prim)
        |> bind (failIfNone (MissingDef prim))
        
    let aframe = lift (frame model >> List.ofSeq >> mkAnd) actions

    lift2 mkAnd2 actions aframe

/// Translates a model axiom into an axiom over a semantic expression.
let translateAxiom model = tryMapTerm (semanticsOf model) ok ok
    
/// Translate a model over Prims to a model over semantic expressions.
let translate model = tryMapAxioms (translateAxiom model) model
