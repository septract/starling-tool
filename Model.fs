module Starling.Model

open Starling.Collections
open Starling.Expr

/// A 'generic' view, parameterised over its parameter type.
type GenView<'a> = Func<'a>

/// A view definition, whose parameters are type-string pairs.
type ViewDef = GenView<Var.Type * string>

/// A view, whose parameters are expressions.
type View = GenView<Expr>

/// A conditional (flat or if-then-else) view.
type CondView = 
    | ITE of BoolExpr * Multiset<CondView> * Multiset<CondView>
    | Func of View

/// A guarded item.
type Guarded<'a> = 
    { Cond : BoolExpr
      Item : 'a }

/// A guarded view.
type GuarView = Guarded<View>

/// A reified view.
type ReView = Guarded<Multiset<View>>

/// A constraint, containing a multiset of views and a Z3 predicate.
type GenConstraint<'a> = 
    { CViews : Multiset<GenView<'a>>
      CExpr : BoolExpr }

/// A model constraint, set over ViewDefs with type-string parameters.
type Constraint = GenConstraint<Var.Type * string>

/// A constraint as used in framed axioms, set over ViewDefs with expression
/// parameters.
type ExprConstraint = GenConstraint<Expr>

/// A pair of conditions.
type ConditionPair<'v> = 
    { Pre : 'v
      Post : 'v }

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

/// A general Hoare triple, consisting of precondition, inner item, and
/// postcondition.
type Hoare<'c, 'i> = 
    { Conditions : ConditionPair<'c>
      Inner : 'i }

type PartConditionPair = ConditionPair<Multiset<CondView>>

type PartHoare<'i> = Hoare<Multiset<CondView>, 'i>

/// A flat axiom, containing a possibly-conditional Hoare triple on an
/// atomic action.
type FlatAxiom = PartHoare<Prim>

/// A fully resolved axiom, containing a guarded Hoare triple on an
/// atomic action.
type FullAxiom = Hoare<Multiset<GuarView>, Prim>

/// A semantically translated axiom, carrying a Z3 Boolean expression as
/// a command.
type SemAxiom = Hoare<Multiset<GuarView>, BoolExpr>

/// An axiom combined with a frame.
type FramedAxiom = 
    { Axiom : SemAxiom
      Frame : Multiset<GuarView> }

/// An unreified term.
type Term = Hoare<Multiset<GuarView>, BoolExpr>

/// A reified term.
type ReTerm = Hoare<Multiset<ReView>, BoolExpr>

/// A partially resolved axiom.
type PartAxiom = 
    | PAAxiom of FlatAxiom
    | PAWhile of isDo : bool * expr : BoolExpr * outer : PartConditionPair * inner : PartHoare<PartAxiom list>
    | PAITE of expr : BoolExpr * outer : PartConditionPair * inTrue : PartHoare<PartAxiom list> * inFalse : PartHoare<PartAxiom list>

/// Extracts the outer condition pair of a part-axiom.
let cpairOfPartAxiom = 
    function 
    | PAAxiom { Conditions = c } -> c
    | PAWhile(outer = c) -> c
    | PAITE(outer = c) -> c

/// A parameterised model of a Starling program.
[<NoComparison>]
type Model<'a, 'c> = 
    { Globals : Var.VarMap
      Locals : Var.VarMap
      Axioms : 'a
      VProtos : Map<string, (Var.Type * string) list>
      // This corresponds to the function D.
      DefViews : 'c }

/// A partly-resolved-axiom model of a Starling program.
type PartModel = Model<PartAxiom list, Constraint list>

/// A flattened model of a Starling program.
type FlatModel = Model<FlatAxiom list, Constraint list>

/// A full model of a Starling program.
type FullModel = Model<FullAxiom list, Constraint list>

/// A semantically translated model of a Starling program.
type SemModel = Model<SemAxiom list, Constraint list>

/// Creates a new model that is the input model with a different axiom set.
/// The axiom set may be of a different type.
let withAxioms (axioms : 'y) (model : Model<'x, 'c>) : Model<'y, 'c> = 
    { Globals = model.Globals
      Locals = model.Locals
      VProtos = model.VProtos
      DefViews = model.DefViews
      Axioms = axioms }
