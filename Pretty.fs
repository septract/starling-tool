namespace Starling

module Pretty =
    /// Pretty-prints expressions.
    /// This is not guaranteed to produce an optimal expression.
    let rec printExpression exp =
        match exp with
            | TrueExp    -> "true"
            | FalseExp   -> "false"
            | IntExp   i -> i.ToString ()
            | IdExp    x -> x
            | MulExp   (a, b) -> printBinop a "*"  b
            | DivExp   (a, b) -> printBinop a "/"  b
            | AddExp   (a, b) -> printBinop a "+"  b
            | SubExp   (a, b) -> printBinop a "-"  b
            | GtExp    (a, b) -> printBinop a ">"  b
            | GeExp    (a, b) -> printBinop a ">=" b
            | LeExp    (a, b) -> printBinop a "<"  b
            | LtExp    (a, b) -> printBinop a "<=" b
            | EqExp    (a, b) -> printBinop a "==" b
            | NeqExp   (a, b) -> printBinop a "!=" b
            | AndExp   (a, b) -> printBinop a "&&" b
            | OrExp    (a, b) -> printBinop a "||" b
    /// Pretty-prints binary operations.
    and printBinop a o b = "(" + printExpression a + o + printExpression b + ")"
