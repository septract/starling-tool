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
        | Instantiate of prim: SMVFunc
                       * error: Starling.Core.Instantiate.Types.Error
        /// A primitive has a missing semantic definition.
        | MissingDef of prim: SMVFunc


/// <summary>
///     Pretty printers used in the Semantics stage.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Instantiate.Pretty

    /// Pretty-prints semantics errors.
    let printSemanticsError =
        function
        | Instantiate (prim, error) ->
          colonSep
              [ fmt "couldn't instantiate primitive '{0}'"
                    [ printSMVFunc prim ]
                Starling.Core.Instantiate.Pretty.printError error ]
        | MissingDef prim ->
            fmt "primitive '{0}' has no semantic definition"
                [ printSMVFunc prim ]



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
        [ Mapper.mapBool xRewrite x
          Mapper.mapBool yRewrite y ]


/// Generates a framing relation for a given variable.
let frameVar par : SMBoolExpr =
    BEq (mkVarExp (After >> Reg) par, mkVarExp (Before >> Reg) par)

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame svars tvars expr =
    // Find all the bound post-variables in the expression...
    let evars =
        expr
        |> varsInBool
        |> Seq.map (valueOf >> regularVarsInSym)
        |> Seq.concat
        |> Seq.choose (function After x -> Some x | _ -> None)
        |> Set.ofSeq

    // Then, for all of the variables in the model, choose those not in evars, and make frame expressions for them.
    Seq.append (Map.toSeq svars) (Map.toSeq tvars)
    // TODO(CaptainHayashi): this is fairly inefficient.
    |> Seq.filter (fun (name, _) -> not (Set.contains name evars))
    |> Seq.map (fun (name, ty) -> frameVar (withType ty name))

/// Translate a primitive command to an expression characterising it.
/// This is the combination of the Prim's action (via emitPrim) and
/// a set of framing terms forcing unbound variables to remain constant
/// (through frame).
let semanticsOfPrim
  (semantics : FuncTable<SVBoolExpr>)
  (svars : VarMap)
  (tvars : VarMap)
  (prim : SMVFunc)
  : Result<SMBoolExpr, Error> =
    (* First, instantiate according to the semantics.
     * This can succeed but return None.  This means there is no
     * entry (erroneous or otherwise) in the semantics for this prim.
     * Since this is an error in this case, make it one.
     *)
    let actions =
        prim
        |> wrapMessages Instantiate
               (instantiate smvParamSubFun semantics)
        |> bind (failIfNone (MissingDef prim))

    let aframe = lift (frame svars tvars >> List.ofSeq >> mkAnd) actions

    lift2 mkAnd2 actions aframe

/// Translate a command to an expression characterising it.
/// This is the sequential composition of the translations of each
/// primitive inside it.
let semanticsOfCommand
  (semantics : FuncTable<SVBoolExpr>)
  (svars : VarMap)
  (tvars : VarMap)
  : Command -> Result<SMBoolExpr, Error> =
    Seq.map (semanticsOfPrim semantics svars tvars)
    >> collect
    >> lift (function
             | [] -> frame svars tvars BTrue |> List.ofSeq |> mkAnd
             | xs -> List.reduce composeBools xs)

/// Translates a model axiom into an axiom over a semantic expression.
let translateAxiom model =
    tryMapTerm
        (semanticsOfCommand model.Semantics model.Globals model.Locals)
        ok
        ok

/// Translate a model over Prims to a model over semantic expressions.
let translate
  (model : UFModel<PTerm<SMGView, SMVFunc>>)
  : Result<UFModel<STerm<SMGView, SMVFunc>>, Error> =
    tryMapAxioms (translateAxiom model) model
