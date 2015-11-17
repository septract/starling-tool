namespace Starling

open Microsoft

module Model =
    /// A 'flattened' (multiset-representation) view.
    type View =
        {
            VName:   string
            VParams: string list
        }

    /// A conditional (flat or if-then-else) view.
    type CondView =
        | CITEView of Z3.BoolExpr * View * View
        | CSetView of View

    /// A constraint, containing a multiset of views and a Z3 predicate.
    type Constraint =
        {
            CViews: View list
            CZ3:    Z3.BoolExpr
        }

    /// A typed inner record of a variable.
    type TVar<'E when 'E :> Z3.Expr> =
        {
            VarExpr:       'E
            VarPreExpr:    'E
            VarPostExpr:   'E
            VarFrameExpr:  'E
        }

    /// A record of a variable in the program model.
    type Var =
        | IntVar  of TVar<Z3.IntExpr>
        | BoolVar of TVar<Z3.BoolExpr>

    /// A model of a Starling program.
    type Model =
        {
            Globals: Map<string, Var>
            Locals:  Map<string, Var>

            // This corresponds to the function D.
            DefViews: Constraint list
        }

    /// An axiom, containing a Hoare triple on an atomic action.
    type Axiom =
        {
            APre: CondView
            ACommand: AST.AtomicAction // TODO(CaptainHayashi): model-ify
            APost: CondView
        }