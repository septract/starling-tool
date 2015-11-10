namespace Starling

open Starling.AST
open Starling.Model
open Starling.Z3

module Pretty =
    /// Pretty-prints lvalues.
    let rec printLValue lv =
        match lv with
            | LVIdent i -> i
            | LVPtr   v -> "*" + printLValue v

    /// Pretty-prints expressions.
    /// This is not guaranteed to produce an optimal expression.
    let rec printExpression exp =
        match exp with
            | TrueExp    -> "true"
            | FalseExp   -> "false"
            | IntExp   i -> i.ToString ()
            | LVExp    x -> printLValue x
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
    and printBinop a o b = "(" + printExpression a + " " + o + " " + printExpression b + ")"

    /// Pretty-prints argument lists.
    let printArgList ss = "(" + String.concat ", " ss + ")"

    /// Pretty-prints views.
    let rec printView v =
        match v with
            | Apply     ( vv,  xs ) -> printView vv + printArgList xs
            | NamedView s           -> s
            | Unit                  -> "emp"
            | Join      ( l, r )    -> printView l + " * " + printView r
            | IfView    ( e, l, r ) -> "if " + printExpression e + " then " + printView l + " else " + printView r

    /// Pretty-prints view lines.
    let printViewLine vl = "{| " + printView vl + " |}"

    /// Pretty-prints constraints.
    let printConstraint cs =
        "constraint " + printView cs.CView + " => " + printExpression cs.CExpression + ";"

    /// Pretty-prints fetch modes.
    let printFetchMode m =
        match m with
            | Direct    -> ""
            | Increment -> "++"
            | Decrement -> "--"

    /// Pretty-prints atomic actions.
    let printAtomicAction atom =
        match atom with
            | CompareAndSwap ( l, f, t ) -> "CAS(" + printLValue l + ", " + printExpression f + ", " + printExpression t
            | Fetch          ( l, r, m ) -> printLValue l + " = " + printLValue r + printFetchMode m
            | Postfix        ( l, m )    -> printLValue l + printFetchMode m

    /// Enters a new line at the given indent level.
    let lnIndent level = "\n" + new string ( ' ', level * 4 )

    /// Pretty-prints commands with the given indent level (in spaces).
    let rec printCommand level cmd =
        match cmd with
            | Atomic  a           -> "<" + printAtomicAction a + ">;"
            | Skip                -> ";"
            | If      ( c, t, f ) -> "if (" + printExpression c + ") " + printBlock level t + " " + printBlock level f
            | While   ( c, b )    -> "while (" + printExpression c + ") " + printBlock level b
            | DoWhile ( b, c )    -> "do " + printBlock level b + " while (" + printExpression c + ")"
            | Blocks  bs          -> List.map ( printBlock level ) bs |> String.concat " || "
            | Assign  ( l, r )    -> printLValue l + " = " + printExpression r + ";"
    /// Pretty-prints viewed commands with the given indent level (in spaces).
    and printViewedCommand level vcom =
        printCommand level vcom.Command + lnIndent level + printViewLine vcom.Post
    /// Pretty-prints blocks with the given indent level (in spaces).
    and printBlock level block =
        "{" + lnIndent ( level + 1 ) + printViewLine block.Pre
            + lnIndent ( level + 1 ) + ( List.map ( printViewedCommand ( level + 1 ) ) block.Contents
                                         |> String.concat ( lnIndent ( level + 1 ) )
                                       )
            + lnIndent level + "}"

    /// Pretty-prints methods.
    let printMethod meth =
        "method " + meth.Name
                  + " " + printArgList meth.Params
                  + " " + printBlock 0 meth.Body

    /// Pretty-prints a variable type.
    let printType t =
        match t with
            | Int  -> "int"
            | Bool -> "bool"

    /// Pretty-prints a script variable of the given class.
    let printScriptVar cls t v =
        cls + " " + printType t + " " + v + ";"

    /// Pretty-prints script lines.
    let printScriptLine sl =
        match sl with
            | SGlobal     ( t, v ) -> printScriptVar "global" t v
            | SLocal      ( t, v ) -> printScriptVar "local" t v
            | SMethod     m        -> printMethod m
            | SConstraint c        -> printConstraint c

    /// Pretty-prints scripts.
    let printScript = List.map printScriptLine >> String.concat "\n\n"

    /// Pretty-prints view conversion errors.
    let printViewConversionError ve =
        match ve with
            | VNotConstrainable view ->
                "cannot use " + printView view
                              + " as subject of a constraint"
    /// Pretty-prints expression conversion errors.
    let printExprConversionError ee =
        match ee with
            | EBadType ( expr, got, want ) ->
                "bad type for Z3 expression " + expr.ToString ()
                                              + ": want " + want
                                              + ", got " + got
            | EBadAST ( ast, reason ) ->
                "cannot convert " + printExpression ast
                                  + " to Z3: " + reason

    /// Pretty-prints constraint conversion errors.
    let printConstraintConversionError ce =
        match ce with
            | CFView ve -> printViewConversionError ve
            | CFExpr ee -> printExprConversionError ee

    /// Pretty-prints variable conversion errors.
    let printVarConversionError ve =
        match ve with
            | VarDup vn -> "variable '" + vn + "' is defined multiple times"

    /// Pretty-prints model conversion errors.
    let printModelConversionError ce =
        match ce with
            | MFConstraint ce -> printConstraintConversionError ce
            | MFVar        ve -> printVarConversionError ve

    /// Pretty-prints a flat view.
    let printModelView v =
        // TODO(CaptainHayashi): sort pretty-printing out so this can move
        v.VName + "(" + String.concat ", " v.VParams + ")"

    /// Pretty-prints a multiset of views.
    let printModelViews vs =
        "[" + String.concat ", " ( List.map printModelView vs ) + "]"

    /// Pretty-prints model variables.
    let printModelVar var =
        var.VarName + ": " + var.VarType.ToString ()

    /// Pretty-prints a model.
    let printModel model =
        "Model: \n" +
            "  Globals: \n    " + String.concat "\n    " (
                List.map printModelVar model.Globals
            ) + "\n\n" +
            "  Locals: \n    " + String.concat "\n    " (
                List.map printModelVar model.Locals
            ) + "\n\n" +
            "  Constraints: \n" + String.concat "\n" (
                List.map (
                    fun c ->
                        "    View: " + printModelViews ( c.CViews )
                                   + "\n"
                                   + "      Z3: " + c.CZ3.ToString ()
                 ) model.DefViews
            )
