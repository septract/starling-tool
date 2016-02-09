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

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>VFunc</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>VFunc</c>.
/// </param>
/// <param name="func">
///   The <c>VFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>VFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>VFunc</c> are its parameters.
///   </para>
/// </remarks>
let subExprInVFunc sub func =
    { func with Params = List.map (subExpr sub) func.Params }

/// A view-definition func.
type DFunc = Func<Var.Type * string>

/// A conditional (flat or if-then-else) func.
type CFunc = 
    | ITE of BoolExpr * Multiset<CFunc> * Multiset<CFunc>
    | Func of VFunc


/// A guarded view func.
type GFunc = Guarded<VFunc>

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>GFunc</c>.
/// </summary>
/// <param name="_arg1">
///   The <c>GFunc</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>GFunc</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>GFunc</c> are the guard itself, and
///     the expressions of the enclosed <c>VFunc</c>.
///   </para>
/// </remarks
let subExprInGFunc sub {Cond = cond; Item = item} =
    { Cond = sub.BSub cond
      Item = subExprInVFunc sub item }

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

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>GView</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>GView</c>.
/// </param>
/// <param name="_arg1">
///   The <c>GView</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>GView</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>GView</c> are those of its constituent
///     <c>GFunc</c>s.
///   </para>
/// </remarks>
let subExprInGView sub = Multiset.map (subExprInGFunc sub)

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

/// A general Hoare triple, consisting of precondition, inner item, and
/// postcondition.
type Axiom<'view, 'command> = 
    { Pre : 'view
      Post : 'view
      Cmd : 'command }

/// Makes an axiom {p}c{q}.
let axiom p c q =
    { Pre = p; Post = q; Cmd = c }

/// An axiom carrying a Prim as its command.
type PAxiom<'a> = Axiom<'a, Prim>

/// An axiom carrying a semantic relation as its command.
type SAxiom<'a> = Axiom<'a, BoolExpr>

/// A partially resolved axiom element.
type PartCmd = 
    | Prim of Prim
    | While of isDo : bool * expr : BoolExpr * inner : Axiom<CView, Axiom<CView, PartCmd> list>
    | ITE of expr : BoolExpr * inTrue : Axiom<CView, Axiom<CView, PartCmd> list> * inFalse : Axiom<CView, Axiom<CView, PartCmd> list>


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

/// <summary>
///   Maps a <c>SubFun</c> over all expressions in a <c>DTerm</c>.
/// </summary>
/// <param name="sub">
///   The <c>SubFun</c> to map over all expressions in the <c>DTerm</c>.
/// </param>
/// <param name="_arg1">
///   The <c>DTerm</c> over which whose expressions are to be mapped.
/// </param>
/// <returns>
///   The <c>DTerm</c> resulting from the mapping.
/// </returns>
/// <remarks>
///   <para>
///     The expressions in a <c>DTerm</c> are those of its constituent
///     command (<c>BoolExpr</c>), its weakest precondition
///     (<c>GView</c>), and its goal (<c>VFunc</c>).
///   </para>
/// </remarks>
let subExprInDTerm sub =
    mapTerm (sub.BSub) (subExprInGView sub) (subExprInVFunc sub)

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
