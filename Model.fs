module Starling.Model

open Microsoft

/// A 'flattened' (multiset-representation) view.
type View =
    // TODO(CaptainHayashi): rename to ViewDef.
    { VName: string
      VParams: string list }

/// A conditional (flat or if-then-else) view.
type CondView =
    // TODO(CaptainHayashi): rename to View.
    | CITEView of Z3.BoolExpr * CondView list * CondView list
    // TODO(CaptainHayashi): expand to all expressions.
    | CSetView of View

/// A constraint, containing a multiset of views and a Z3 predicate.
type Constraint =
    { CViews: View list
      CZ3: Z3.BoolExpr }

/// A typed inner record of a variable.
type TVar<'E when 'E :> Z3.Expr> =
    { VarExpr: 'E
      VarPreExpr: 'E
      VarPostExpr: 'E
      VarFrameExpr: 'E }

/// A record of a variable in the program model.
type Var =
    | IntVar of TVar<Z3.IntExpr>
    | BoolVar of TVar<Z3.BoolExpr>

/// A pair of conditions.
type ConditionPair =
    { Pre: CondView list
      Post: CondView list }

/// A modelled primitive command.
type Prim =
    | ArithFetch of dest: AST.LValue option * src: AST.LValue * mode: AST.FetchMode
    | BoolFetch of dest: AST.LValue option * src: AST.LValue
    | ArithCAS of dest: AST.LValue * test: AST.LValue * set: Z3.ArithExpr
    | BoolCAS of dest: AST.LValue * test: AST.LValue * set: Z3.BoolExpr
    | ArithLocalSet of dest: AST.LValue * src: Z3.ArithExpr
    | BoolLocalSet of dest: AST.LValue * src: Z3.BoolExpr
    | PrimId
    | PrimAssume of Z3.BoolExpr

/// A general Hoare triple, consisting of precondition, inner item, and
/// postcondition.
type Hoare<'a> =
    { Conditions: ConditionPair 
      Inner: 'a }

/// An axiom, containing a Hoare triple on an atomic action.
type Axiom = Hoare<Prim list>

/// A partially resolved axiom.
type PartAxiom =
    | PAAxiom of Axiom
    | PAWhile of isDo: bool * expr: Z3.BoolExpr * outer: ConditionPair * inner: Hoare<PartAxiom list>
    | PAITE of expr: Z3.BoolExpr * outer: ConditionPair * inTrue: Hoare<PartAxiom list> * inFalse: Hoare<PartAxiom list>

/// Extracts the outer condition pair of a part-axiom.
let cpairOfPartAxiom pa =
    match pa with
    | PAAxiom a -> a.Conditions
    | PAWhile (outer = o) -> o
    | PAITE (outer = o) -> o

/// A model of a Starling program.
type PartModel<'g, 'l, 'a, 'c> =
    { Context: Z3.Context

      Globals: 'g
      Locals:  'l
      Axioms:  'a

      // This corresponds to the function D.
      DefViews: 'c }

/// A variable map
type VarMap = Map<string, Var>

/// A full model of a Starling program.
type Model = PartModel<VarMap, VarMap, PartAxiom list, Constraint list>

/// A flattened model of a Starling program.
type FlatModel = PartModel<VarMap, VarMap, Axiom list, Constraint list>

/// Disposes the Z3 context inside a Model.
let disposeZ3 model = model.Context.Dispose ()

/// Creates a new model that is the input model with a different axiom set.
/// The axiom set may be of a different type.
let withAxioms (axioms: 'y) (model: PartModel<'g, 'l, 'x, 'c>): PartModel<'g, 'l, 'y, 'c> =
    { Context = model.Context
      Globals = model.Globals
      Locals = model.Locals
      DefViews = model.DefViews
      Axioms = axioms }

