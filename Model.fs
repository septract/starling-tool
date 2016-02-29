/// <summary>
///   Module of model types and functions.
/// </summary>
module Starling.Model

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Expr
open Starling.Var.Pretty
open Starling.Pretty.Expr
open Starling.Pretty.Types

(*
 * Starling uses the following general terminology for model items.
 * (Note that these terms differ from their CamelCasedAndPrefixed
 * counterparts, whose meanings are given in their documentation comments.)
 *
 * func: a single term, usually Name(p1, p2, .., pn), in a view.
 *
 * view: an entire view expression, or multiset, of funcs.
 *
 * guarded: Starling represents case splits in its proof theory by
 *          surrounding a view or func whose presence in the proof is
 *          conditional with an expression true if or only if it is
 *          present; such a view or func is 'guarded'.
 *
 * view-set: a multiset of guarded views.
 *
 * conds: a pair of view assertions.
 * 
 * axiom: a Hoare triple, containing a pair of conds, and some
 *        representation of a command.
 *
 * prim: a structured representation of an axiom command.
 *)


(*
 * Guards
 *)

/// A guarded item.
/// The semantics of a Guarded Item is that the Item is to be taken as present
/// in its parent context (eg a View) if, and only if, Cond holds.
type Guarded<'a> = 
    { Cond : BoolExpr
      Item : 'a }


(*
 * Funcs (other than Starling.Collections.Func)
 *)

/// A func over expressions, used in view expressions.
type VFunc = Func<Expr>

/// A view-definition func.
type DFunc = Func<Var.Type * string>

/// A guarded view func.
type GFunc = Guarded<VFunc>


(*
 * Views
 *)

/// <summary>
///   A basic view, as a multiset of VFuncs.
/// </summary>
/// <remarks>
///   Though View is the canonical Concurrent Views Framework view,
///   we actually seldom use it.
/// </remarks>
type View = Multiset<VFunc>

/// A view definition.
type DView = Multiset<DFunc>

/// <summary>
///   A guarded view.
/// </summary>
/// <remarks>
///   These are the most common form of view in Starling internally,
///   although theoretically speaking they are equivalent to Views
///   with the guards lifting to proof case splits.
/// </remarks>
type GView = Multiset<GFunc>


(*
 * View sets
 *)

/// A set of guarded views, as produced by reification.
type ViewSet = Multiset<Guarded<View>>


(*
 * View definitions
 *)

/// <summary>
///   A view definition.
/// </summary>
/// <remarks>
///   The semantics of a ViewDef is that, if Def is present, then the
///   view View is satisfied if, and only if, Def holds.
/// </remarks>
type ViewDef<'view> =
    { View : 'view
      Def : BoolExpr option }


(*
 * Terms
 *)

/// <summary>
///   A term, containing a command relation, weakest precondition, and goal.
/// </summary>
/// <remarks>
///   Though these are similar to Axioms, we keep them separate for reasons of
///   semantics: Axioms are literal Hoare triples {P}C{Q}, whereas Terms are
///   some form of the actual Views axiom soundness check we intend to prove.
/// </remarks>
type Term<'cmd, 'wpre, 'goal> =
    { /// The command relation of the Term.
      Cmd : 'cmd
      /// The weakest precondition of the Term.
      WPre : 'wpre
      /// The intended goal of the Term, ie the frame to preserve.
      Goal : 'goal
    }

/// A term over <c>VFunc</c>-encoded commands.
type PTerm<'wpre, 'goal> = Term<VFunc, 'wpre, 'goal>

/// A term over semantic-relation commands.
type STerm<'wpre, 'goal> = Term<BoolExpr, 'wpre, 'goal>

/// <summary>
///   A 'Datalog-style' term of one goal <c>VFunc</c> and a
///   weakest-precondition <c>GView</c>.
/// </summary>
type DTerm = STerm<GView, VFunc>

/// A term using only internal boolean expressions.
type FTerm = STerm<BoolExpr, BoolExpr>

/// Rewrites a Term by transforming its Cmd with fC, its WPre with fW,
/// and its Goal with fG.
let mapTerm fC fW fG {Cmd = c; WPre = w; Goal = g} =
    {Cmd = fC c; WPre = fW w; Goal = fG g}

/// Rewrites a Term by transforming its Cmd with fC, its WPre with fW,
/// and its Goal with fG.
/// fC, fW and fG must return Chessie results; liftMapTerm follows suit. 
let tryMapTerm fC fW fG {Cmd = c; WPre = w; Goal = g} =
    trial {
        let! cR = fC c;
        let! wR = fW w;
        let! gR = fG g;
        return {Cmd = cR; WPre = wR; Goal = gR}
    }


(*
 * Models
 *)

/// A parameterised model of a Starling program.
type Model<'axiom, 'dview> = 
    { Globals : Var.VarMap
      Locals : Var.VarMap
      Axioms : 'axiom list
      /// <summary>
      ///   The semantic function for this model.
      /// </summary>
      Semantics : (DFunc * BoolExpr) list
      // This corresponds to the function D.
      ViewDefs : ViewDef<'dview> list }

/// Returns the axioms of a model.
let axioms {Axioms = xs} = xs

/// Creates a new model that is the input model with a different axiom set.
/// The axiom set may be of a different type.
let withAxioms (xs : 'y list) (model : Model<'x, 'dview>) : Model<'y, 'dview> = 
    { Globals = model.Globals
      Locals = model.Locals
      ViewDefs = model.ViewDefs
      Semantics = model.Semantics
      Axioms = xs }

/// Maps a pure function f over the axioms of a model.
let mapAxioms (f : 'x -> 'y) (model : Model<'x, 'dview>) : Model<'y, 'dview> =
    withAxioms (model |> axioms |> List.map f) model

/// Maps a failing function f over the axioms of a model.
let tryMapAxioms (f : 'x -> Result<'y, 'e>) (model : Model<'x, 'dview>) : Result<Model<'y, 'dview>, 'e> =
    lift (fun x -> withAxioms x model)
         (model |> axioms |> List.map f |> collect)


(*
 * Pretty printers
 *)

module Pretty =
    /// Pretty-prints a type-name parameter.
    let printParam (ty, name) = 
        hsep [ ty |> printType
               name |> String ]

    /// Pretty-prints a multiset given a printer for its contents.
    let printMultiset pItem = 
        Multiset.toList
        >> List.map pItem
        >> semiSep

    /// Pretty-prints a guarded item.
    let printGuarded pitem {Cond = c; Item = i} = 
        // Don't bother showing the guard if it's always true.
        if Expr.isTrue c then pitem i
        else 
            parened (HSep([ printBoolExpr c
                            pitem i ], String "|"))

    /// Pretty-prints a VFunc.
    let printVFunc = printFunc printExpr

    /// Pretty-prints a guarded view.
    let printGFunc = printGuarded printVFunc

    /// Pretty-prints a DFunc.
    let printDFunc = printFunc printParam

    /// Pretty-prints a View.
    let printView = printMultiset printVFunc

    /// Pretty-prints a DView.
    let printDView = printMultiset printDFunc >> squared

    /// Pretty-prints a GView.
    let printGView = printMultiset printGFunc >> ssurround "<|" "|>"

    /// Pretty-prints a view set.
    let printViewSet = printMultiset (printGuarded printView >> ssurround "((" "))") >> ssurround "(|" "|)"

    /// Type of model view.
    type ModelView =
        /// View the entire model.
        | Model
        /// View the model's terms.
        | Terms
        /// View a specific term.
        | Term of int
