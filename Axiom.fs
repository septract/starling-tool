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
open Starling.Core.View
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.GuardedView
open Starling.Core.TypeSystem


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
    type GoalAxiom<'cmd> =
        { /// The axiom to be checked for soundness under Goal.
          Axiom : Axiom<GView<Sym<Var>>, 'cmd>
          /// The view representing the goal for any terms over Axiom.
          Goal : OView }

/// <summary>
///     Pretty printers for axioms.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    open Starling.Core.Model.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.GuardedView.Pretty

    /// Pretty-prints an Axiom, given knowledge of how to print its views
    /// and command.
    let printAxiom (pView : 'view -> Doc)
                   (pCmd : 'cmd -> Doc)
                   ({ Pre = pre; Post = post; Cmd = cmd } : Axiom<'view, 'cmd>)
                   : Doc =
        Surround(pre |> pView, cmd |> pCmd, post |> pView)

    /// Pretty-prints a goal axiom.
    let printGoalAxiom (printCmd : 'cmd -> Doc)
                       ({ Axiom = a; Goal = f } : GoalAxiom<'cmd>)
                       : Doc =
        vsep [ headed "Axiom"
                      (a |> printAxiom printSVGView printCmd |> Seq.singleton)
               headed "Goal" (f |> printOView |> Seq.singleton) ]


/// Makes an axiom {p}c{q}.
let axiom (p : 'view) (c : 'cmd) (q : 'view)
          : Axiom<'view, 'cmd> =
    { Pre = p; Post = q; Cmd = c }


(*
 * GoalAxioms
 *)

/// Instantiates a defining view into a view expression.
let instantiateGoal (fg : FreshGen)
                    (dvs : DView)
                    : OView =
    let instantiateParam = mkVarExp (goalVar fg >> Reg)

    dvs |> List.map (fun { Name = n; Params = ps } ->
               { Name = n
                 Params = List.map instantiateParam ps })

/// Converts an axiom into a list of framed axioms, by combining it with the
/// defining views of a model.
let goalAddAxiom
  (ds : ViewDef<DView, _> list)
  (fg : FreshGen)
  ((name, axiom) : (string * Axiom<GView<Sym<Var>>, 'cmd>))
  : (string * GoalAxiom<'cmd>) list =
    // Each axiom comes in with a name like method_0,
    // where the 0 is the edge number.
    // This appends the viewdef number after the edge number.
    List.mapi
        (fun i (DefOver vs) ->
            (sprintf "%s_%03d" name i,
             { Axiom = axiom
               Goal = instantiateGoal fg vs }))
        ds

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
let goalAdd
  (mdl : Model<Axiom<GView<Sym<Var>>, 'cmd>, _>)
  : Model<GoalAxiom<'cmd>, _> =
    // We use a fresh ID generator to ensure every goal variable is unique.
    let fg = freshGen ()

    let { ViewDefs = ds; Axioms = xs } = mdl
    let xs' =
        xs |> Map.toList |> concatMap (goalAddAxiom ds fg) |> Map.ofList

    withAxioms xs' mdl
