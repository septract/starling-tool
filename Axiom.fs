/// <summary>
///     The <c>Axiom</c> type, pretty printers, and related functions.
///
///     <para>
///         As in Views, <c>Axiom</c>s in Starling are triples (p, c, q),
///         where p and q are views and c is some form of atomic command.
///         They are distinct from <c>Term</c>s, which model the
///         individual terms of an axiom soundness proof.
///     </para>
/// </summary>
module Starling.Core.Axiom

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView


/// <summary>
///     Types for axioms.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A general Hoare triple.
    ///
    ///     <para>
    ///         An <c>Axiom</c> contains a precondition, inner command, and
    ///         postcondition.
    ///     </para>
    /// </summary>
    type Axiom<'view, 'cmd> =
        { /// <summary>
          ///     The precondition of the axiom.
          /// </summary>
          Pre : 'view
          /// <summary>
          ///     The postcondition of the axiom.
          /// </summary>
          Post : 'view
          /// <summary>
          ///     The command of the axiom.
          /// </summary>
          Cmd : 'cmd }

    /// An axiom combined with a goal view.
    type GoalAxiom =
        { /// The axiom to be checked for soundness under Goal.
          Axiom : Axiom<SMGView, Command>
          /// The view representing the goal for any terms over Axiom.
          Goal : OView }

/// <summary>
///     Pretty printers for axioms.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    open Starling.Core.Model.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.GuardedView.Pretty

    /// Pretty-prints an Axiom, given knowledge of how to print its views
    /// and command.
    let printAxiom pCmd pView { Pre = pre; Post = post; Cmd = cmd } =
        Surround(pre |> pView, cmd |> pCmd, post |> pView)

    /// Pretty-prints a goal axiom.
    let printGoalAxiom { Axiom = a; Goal = f } =
        vsep [ headed "Axiom"
                      (a |> printAxiom printCommand printSMGView |> Seq.singleton)
               headed "Goal" (f |> printOView |> Seq.singleton) ]


/// Makes an axiom {p}c{q}.
let axiom p c q =
    { Pre = p; Post = q; Cmd = c }


(*
 * GoalAxioms
 *)

/// Given a fresh generator, yields a function promoting a string to a
/// goal variable.
let goalVar (fg : FreshGen) = (fg |> getFresh |> curry Goal) >> Reg

/// Instantiates a view parameter.
let instantiateParam fg =
    mkVarExp (goalVar fg)

/// Instantiates a defining view into a view expression.
let instantiateGoal fg dvs =
    dvs |> List.map (fun { Name = n; Params = ps } ->
               { Name = n
                 Params = List.map (instantiateParam fg) ps })

/// Converts an axiom into a list of framed axioms, by combining it with the
/// defining views of a model.
let goalAddAxiom ds fg (name, axiom) =
    // Each axiom comes in with a name like method_0,
    // where the 0 is the edge number.
    // This appends the viewdef number after the edge number.
    List.mapi
        (fun i (DefOver vs) ->
            (sprintf "%s_%d" name i,
             { Axiom = axiom
               Goal = instantiateGoal fg vs }))
        ds

/// <summary>
///     Converts the axioms of a <c>Model</c> into <c>GoalAxiom</c>s.
///
///     <para>
///         <c>GoalAxiom</c>s are a Cartesian product of the existing axioms
///         and the domain of the <c>ViewDefs</c> map.
///     </para>
/// </summary>
/// <param name="_arg1">
///     The <c>Model</c> to convert.
/// </param>
/// <returns>
///     The new axiom map, over <c>GoalAxiom</c>s.
/// </returns>
let goalAddAxioms {ViewDefs = ds; Axioms = xs} =
    // We use a fresh ID generator to ensure every goal variable is unique.
    let fg = freshGen ()

    xs
    |> Map.toList
    |> concatMap (goalAddAxiom ds fg)
    |> Map.ofList

/// <summary>
///     Converts a model into one over <c>GoalAxiom</c>s.
///
///     <para>
///         <c>GoalAxiom</c>s are a Cartesian product of the existing axioms
///         and the domain of the <c>ViewDefs</c> map.
///     </para>
/// </summary>
/// <param name="mdl">
///     The <c>Model</c> to convert.
/// </param>
/// <returns>
///     The new <c>Model</c>, over <c>GoalAxiom</c>s.
/// </returns>
let goalAdd mdl = withAxioms (goalAddAxioms mdl) mdl
