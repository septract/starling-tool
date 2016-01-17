/// <summary>
///   Module of model types and functions.
/// </summary>
module Starling.Model

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Expr

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

/// A conditional (flat or if-then-else) func.
type CFunc = 
    | ITE of BoolExpr * Multiset<CFunc> * Multiset<CFunc>
    | Func of VFunc

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

/// A conditional view, or multiset of CFuncs.
type CView = Multiset<CFunc>

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
 * Prims
 *)

/// A modelled primitive command.
type Prim = 
    | IntLoad of dest : Var.LValue option * src : Var.LValue * mode : Var.FetchMode
    | BoolLoad of dest : Var.LValue * src : Var.LValue
    | IntStore of dest : Var.LValue * src : ArithExpr
    | BoolStore of dest : Var.LValue * src : BoolExpr
    | IntCAS of dest : Var.LValue * test : Var.LValue * set : ArithExpr
    | BoolCAS of dest : Var.LValue * test : Var.LValue * set : BoolExpr
    | IntLocalSet of dest : Var.LValue * src : ArithExpr
    | BoolLocalSet of dest : Var.LValue * src : BoolExpr
    | PrimId
    | PrimAssume of BoolExpr


(*
 * Conds and axioms
 *)

/// A pair of conditions.
type Conds<'v> = 
    { Pre : 'v
      Post : 'v }

/// A general Hoare triple, consisting of precondition, inner item, and
/// postcondition.
type Axiom<'c, 'i> = 
    { Conds : Conds<'c>
      Cmd : 'i }

/// Makes an axiom {p}c{q}.
let axiom p c q =
    { Conds = { Pre = p; Post = q }; Cmd = c }

/// An axiom carrying a Prim as its command.
type PAxiom<'a> = Axiom<'a, Prim>

/// An axiom carrying a semantic relation as its command.
type SAxiom<'a> = Axiom<'a, BoolExpr>

/// A partially resolved axiom.
type PartAxiom = 
    | PAAxiom of PAxiom<CView>
    | PAWhile of isDo : bool * expr : BoolExpr * outer : Conds<CView> * inner : Axiom<CView, PartAxiom list>
    | PAITE of expr : BoolExpr * outer : Conds<CView> * inTrue : Axiom<CView, PartAxiom list> * inFalse : Axiom<CView, PartAxiom list>

/// Extracts the outer condition pair of a part-axiom.
let cpairOfPartAxiom = 
    function 
    | PAAxiom { Conds = c } -> c
    | PAWhile(outer = c) -> c
    | PAITE(outer = c) -> c


(*
 * Framed axioms
 *)

/// An axiom combined with a framing guarded view.
type FramedAxiom = 
    { /// The axiom to be checked for soundness under Frame.
      Axiom : SAxiom<GView>
      /// The view to be preserved by Axiom.
      Frame : View }


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

/// A term over semantic-relation commands.
type STerm<'wpre, 'goal> = Term<BoolExpr, 'wpre, 'goal>


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
      Axioms = xs }

/// Maps a pure function f over the axioms of a model.
let mapAxioms (f : 'x -> 'y) (model : Model<'x, 'dview>) : Model<'y, 'dview> =
    withAxioms (model |> axioms |> List.map f) model

/// Maps a failing function f over the axioms of a model.
let tryMapAxioms (f : 'x -> Result<'y, 'e>) (model : Model<'x, 'dview>) : Result<Model<'y, 'dview>, 'e> =
    lift (fun x -> withAxioms x model)
         (model |> axioms |> List.map f |> collect)
