namespace Starling

open Microsoft

module Model =
    /// A 'flattened' (multiset-representation) view.
    type View =
        {
            VName  : string
            VParams: string list
        }

    /// Pretty-prints a flat view.
    let printView v =
        // TODO(CaptainHayashi): sort pretty-printing out so this can move
        v.VName + "(" + String.concat ", " v.VParams + ")"

    /// A constraint, containing a multiset of views and a Z3 predicate.
    type Constraint =
        {
            CViews: View list
            CZ3:    Z3.BoolExpr
        }