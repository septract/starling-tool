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



/// <summary>
///     Composes two Boolean expressions representing commands.
///     <para>
///         The pre-state of the first and post-state of the second become
///         the pre- and post- state of the composition.  All of the
///         intermediates (and pre-state) in the second are raised to the
///         highest intermediate level in the first.  The post-state
///         of the first then becomes the lowest intermediate level in the
///         second.
///     </para>
/// </summary>
/// <param name="x">
///     The first expression to compose.
/// </param>
/// <param name="y">
///     The second expression to compose.
/// </param>
/// <returns>
///     The result of composing <paramref name="y" /> onto
///     <paramref name="x" /> as above.
/// </returns>
let composeBools x y =
    (* Find out what the next intermediate level is on x:
     * this is going to replace !before in y, and each intermediate level
     * in y will increase by this level plus one.
     *)
    let nLevel = nextBoolIntermediate x

    let xRewrite =
        function
        | After v -> Reg (Intermediate (nLevel, v))
        | v -> Reg v
        |> (fun f ->
                Mapper.compose
                    (Mapper.cmake f)
                    (Mapper.make AVar BVar))
        |> liftVToSym
        |> onVars

    let yRewrite =
        function
        | Before v -> Reg (Intermediate (nLevel, v))
        | Intermediate (i, v) -> Reg (Intermediate (i + nLevel + 1I, v))
        | v -> Reg v
        |> (fun f ->
                Mapper.compose
                    (Mapper.cmake f)
                    (Mapper.make AVar BVar))
        |> liftVToSym
        |> onVars

    mkAnd
        [ Mapper.mapBoolCtx xRewrite NoCtx x |> snd
          Mapper.mapBoolCtx yRewrite NoCtx y |> snd ]


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
  (svars : VarMap)
  (tvars : VarMap)
  (prim : PrimCommand)
  : Result<SMBoolExpr, Error> =
    (* First, instantiate according to the semantics.
     * This can succeed but return None.  This means there is no
     * entry (erroneous or otherwise) in the semantics for this prim.
     * Since this is an error in this case, make it one.
     *)
    prim
    |> wrapMessages Instantiate
           (instantiatePrim primSubFun semantics)
    |> bind (failIfNone (MissingDef prim))

/// Given some mapping Map<Var, bigint option> mapping names to intermediate values
/// create the sequentially composed x, replacing before's and after's
open Starling.Core.Pretty
open Starling.Core.Expr.Pretty
open Starling.Core.Var.Pretty
open Starling.Core.Symbolic.Pretty
let seqComposition xs =

    // since we are trying to keep track of explicit state (where we are in terms of the intermediate variables)
    // it's _okay_ to include actual mutable state here!
    let mutable dict = System.Collections.Generic.Dictionary<Var, bigint>()

    let mapper x =
        let nLevel = nextBoolIntermediate x
        let dict2 = System.Collections.Generic.Dictionary<Var, bigint>(dict)

        let xRewrite =
            function
            | Before v as v' ->
                if dict.ContainsKey (v) then
                    let iv = dict.[v]
                    Reg (Intermediate(iv, v))
                else
                    Reg v'
            | After v ->
                if dict2.ContainsKey(v) then
                    ignore <| dict2.Remove(v)

                dict2.Add(v, nLevel)
                Reg (Intermediate (nLevel, v))
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
    Seq.map (instantiateSemanticsOfPrim semantics svars tvars)
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
