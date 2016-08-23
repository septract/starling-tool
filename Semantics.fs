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
open Starling.Core.TypeSystem
open Starling.Core.Command
open Starling.Core.Command.Compose
open Starling.Core.GuardedView
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Sub
open Starling.Core.Instantiate


/// <summary>
///     Types used in the Semantics stage.
/// </summary>
[<AutoOpen>]
module Types =
    /// Type of errors relating to semantics instantiation.
    type Error =
        /// There was an error instantiating a semantic definition.
        | Instantiate of prim: PrimCommand
                       * error: Starling.Core.Instantiate.Types.Error
        /// A primitive has a missing semantic definition.
        | MissingDef of prim: PrimCommand


/// <summary>
///     Pretty printers used in the Semantics stage.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Instantiate.Pretty

    /// Pretty-prints semantics errors.
    let printSemanticsError =
        function
        | Instantiate (prim, error) ->
          colonSep
              [ fmt "couldn't instantiate primitive '{0}'"
                    [ printPrimCommand prim ]
                Starling.Core.Instantiate.Pretty.printError error ]
        | MissingDef prim ->
            fmt "primitive '{0}' has no semantic definition"
                [ printPrimCommand prim ]

/// Generates a framing relation for a given variable.
let frameVar ctor par : SMBoolExpr =
    BEq (mkVarExp (After >> Reg) par, mkVarExp (ctor >> Reg) par)

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame svars tvars expr =
    // Find all the bound post-variables in the expression...
    let evars =
        expr
        |> mapOverSMVars Mapper.mapBoolCtx findSMVars
        |> Seq.map valueOf
        |> Seq.choose (function After x -> Some x | _ -> None)
        |> Set.ofSeq

    // Then, for all of the variables in the model, choose those not in evars, and make frame expressions for them.
    Seq.append (Map.toSeq svars) (Map.toSeq tvars)
    // TODO(CaptainHayashi): this is fairly inefficient.
    |> Seq.filter (fun (name, _) -> not (Set.contains name evars))
    |> Seq.choose (fun (name, ty) ->
        let next = getBoolIntermediate name expr
        match next with
        | None   -> Some (name, ty, Before)
        | Some i -> Some (name, ty, (fun x -> (Intermediate(i, x)))))
    |> Seq.map (fun (name, ty, ctor) -> frameVar ctor (withType ty name))

/// Translate a primitive command to an expression characterising it
/// by instantiating the semantics from the core semantics map with
/// the variables from the command
let instantiateSemanticsOfPrim
  (semantics : PrimSemanticsMap)
  (prim : PrimCommand)
  : Result<SMBoolExpr, Error> =
    (* First, instantiate according to the semantics.
     * This can succeed but return None.  This means there is no
     * entry (erroneous or otherwise) in the semantics for this prim.
     * Since this is an error in this case, make it one.
     *)
    prim
    |> wrapMessages Instantiate (instantiatePrim semantics)
    |> bind (failIfNone (MissingDef prim))

/// Given a list of BoolExpr's it sequentially composes them together
/// this works by taking each BoolExpr in turn,
///     converting *all* After variables to (Intermediate i) variables
///     converts any Before variables where an Intermediate exists, to that Intermediate
///
/// the frame can then be constructed by taking the BoolExpr and looking for the aforementioned Intermediate 
/// variables and adding a (= (After v) (Intermediate maxInterValue v)) if it finds one
let seqComposition xs =
    // since we are trying to keep track of explicit state (where we are in terms of the intermediate variables)
    // it's _okay_ to include actual mutable state here!
    let mutable dict = System.Collections.Generic.Dictionary<Var, bigint>()

    let mapper x =
        let dict2 = System.Collections.Generic.Dictionary<Var, bigint>(dict)
        let isSet = System.Collections.Generic.HashSet<Var>()

        let xRewrite =
            function
            | Before v as v' ->
                if dict.ContainsKey (v) then
                    let iv = dict.[v]
                    Reg (Intermediate(iv, v))
                else
                    Reg v'
            | After v ->
                /// Have not set After v to a new Intermediate yet
                if not (isSet.Contains(v)) then
                    ignore <| isSet.Add(v)

                    if dict2.ContainsKey(v) then
                        let nLevel = dict2.[v] + 1I
                        ignore <| dict2.Remove(v)
                        dict2.Add(v, nLevel)
                        Reg (Intermediate (nLevel, v))
                    else
                        dict2.Add(v, 0I)
                        Reg (Intermediate (0I, v))
                else
                    Reg (Intermediate (dict2.[v], v))
            | v -> Reg v
            |> (fun f ->
                    Mapper.compose
                        (Mapper.cmake f)
                        (Mapper.make AVar BVar))
            |> liftVToSym
            |> onVars

        let bexpr = Mapper.mapBoolCtx xRewrite NoCtx x |> snd
        dict <- dict2
        bexpr

    let rec mapping =
        function
        | []        ->  BTrue
        | x :: ys   ->  mkAnd2 (mapper x) (mapping ys)

    mapping xs

/// Given a BoolExpr add the frame and return the new BoolExpr
let addFrame svars tvars bexpr =
    mkAnd2 (frame svars tvars bexpr |> List.ofSeq |> mkAnd)
           bexpr

/// Translate a command to an expression characterising it.
/// This is the sequential composition of the translations of each
/// primitive inside it.
let semanticsOfCommand
  (semantics : PrimSemanticsMap)
  (svars : VarMap)
  (tvars : VarMap)
  : Command -> Result<SMBoolExpr, Error> =
    // Instantiate the semantic function of each primitive
    Seq.map (instantiateSemanticsOfPrim semantics)
    >> collect

    // Compose them together with intermediates
    >> lift seqComposition

    // Add the frame
    >> lift (addFrame svars tvars)

open Starling.Core.Axiom.Types
/// Translate a model over Prims to a model over semantic expressions.
let translate
  (model : Model<GoalAxiom<Command>, 'viewdef>)
  : Result<Model<GoalAxiom<SMBoolExpr>, 'viewdef>, Error> =
    let modelSemantics = semanticsOfCommand model.Semantics model.Globals model.Locals
    let replaceCmd ga c = { Goal = ga.Goal; Axiom = {Pre = ga.Axiom.Pre; Post = ga.Axiom.Post; Cmd = c }}
    let transSem ga = bind (replaceCmd ga >> ok) (modelSemantics ga.Axiom.Cmd)
    tryMapAxioms transSem model
