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

open Starling.Core.Model


/// <summary>
///     Types for axioms.
/// </summary>
[<AutoOpen>]
module Types =
    /// A general Hoare triple, consisting of precondition, inner item, and
    /// postcondition.
    type Axiom<'view, 'cmd> = 
        { Pre : 'view
          Post : 'view
          Cmd : 'cmd }

    /// An axiom with a VFunc as its command.
    type PAxiom<'view> = Axiom<'view, VFunc>

    /// An axiom combined with a framing guarded view.
    type FramedAxiom = 
        { /// The axiom to be checked for soundness under Frame.
          Axiom : PAxiom<GView>
          /// The view to be preserved by Axiom.
          Frame : View }

/// <summary>
///     Pretty printers for axioms.
/// </summary>
module Pretty =
    open Starling.Pretty.Types

    open Starling.Core.Model.Pretty
    
    /// Pretty-prints an Axiom, given knowledge of how to print its views
    /// and command.
    let printAxiom pCmd pView { Pre = pre; Post = post; Cmd = cmd } = 
        Surround(pre |> pView, cmd |> pCmd, post |> pView)

    /// Pretty-prints a PAxiom.
    let printPAxiom pView = printAxiom printVFunc pView    

    /// Pretty-prints a framed axiom.
    let printFramedAxiom {Axiom = a; Frame = f} = 
        vsep [ headed "Axiom" (a |> printPAxiom printGView |> Seq.singleton)
               headed "Frame" (f |> printView |> Seq.singleton) ]


/// Makes an axiom {p}c{q}.
let axiom p c q =
    { Pre = p; Post = q; Cmd = c }
