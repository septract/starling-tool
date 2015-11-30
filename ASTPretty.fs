module Starling.Pretty.AST

open Starling.AST
open Starling.Var
open Starling.Pretty.Types

/// Pretty-prints lvalues.
let rec printLValue lv =
    match lv with
    | LVIdent i -> i
    //| LVPtr v -> "*" + printLValue v

/// Pretty-prints Boolean operations.
let printBop bop =
    match bop with
    | Mul -> "*"
    | Div -> "/"
    | Add -> "+"
    | Sub -> "-"
    | Gt -> ">"
    | Ge -> ">="
    | Le -> "<"
    | Lt -> "<="
    | Eq -> "=="
    | Neq -> "!="
    | And -> "&&"
    | Or -> "||"


/// Pretty-prints expressions.
/// This is not guaranteed to produce an optimal expression.
let rec printExpression exp =
    match exp with
    | TrueExp -> "true"
    | FalseExp -> "false"
    | IntExp i -> i.ToString ()
    | LVExp x -> printLValue x
    | BopExp (op, a, b) ->
        "(" + printExpression a + " " + printBop op + " " + printExpression b + ")"

/// Pretty-prints argument lists.
let printArgList argp ss = "(" + String.concat ", " ( List.map argp ss ) + ")"

/// Pretty-prints views.
let rec printView v =
    match v with
    | Func (vv, xs) -> vv + printArgList printExpression xs
    | Unit -> "emp"
    | Join (l, r) -> printView l + " * " + printView r
    | IfView (e, l, r) -> "if " + printExpression e + " then " + printView l + " else " + printView r

/// Pretty-prints view definitions.
let rec printViewDef v =
    match v with
    | DFunc (vv, xs) -> vv + printArgList id xs
    | DUnit -> "emp"
    | DJoin (l, r) -> printViewDef l + " * " + printViewDef r

/// Pretty-prints view lines.
let printViewLine vl = "{| " + printView vl + " |}"

/// Pretty-prints constraints.
let printConstraint cs =
    "constraint " + printViewDef cs.CView + " => " + printExpression cs.CExpression + ";"

/// Pretty-prints fetch modes.
let printFetchMode m =
    match m with
    | Direct -> ""
    | Increment -> "++"
    | Decrement -> "--"

/// Pretty-prints atomic actions.
let printAtomicAction atom =
    match atom with
    | CompareAndSwap (l, f, t) -> "CAS(" + printLValue l + ", " + printLValue f + ", " + printExpression t
    | Fetch (l, r, m) -> printLValue l + " = " + printLValue r + printFetchMode m
    | Postfix (l, m) -> printLValue l + printFetchMode m
    | Id -> "id"
    | Assume e -> "assume(" + printExpression e + ")"

/// Pretty-prints commands with the given indent level (in spaces).
let rec printCommand level cmd =
    match cmd with
    | Atomic a -> "<" + printAtomicAction a + ">;"
    | Skip -> ";"
    | If (c, t, f) -> "if (" + printExpression c + ") " + printBlock level t + " " + printBlock level f
    | While (c, b) -> "while (" + printExpression c + ") " + printBlock level b
    | DoWhile (b, c) -> "do " + printBlock level b + " while (" + printExpression c + ")"
    | Blocks bs -> List.map (printBlock level) bs |> String.concat " || "
    | Assign (l, r) -> printLValue l + " = " + printExpression r + ";"
/// Pretty-prints viewed commands with the given indent level (in spaces).
and printViewedCommand level vcom =
    printCommand level vcom.Command + lnIndent level + printViewLine vcom.Post
/// Pretty-prints blocks with the given indent level (in spaces).
and printBlock level block =
    "{" + lnIndent (level + 1) + printViewLine block.Pre
        + lnIndent (level + 1) + (List.map (printViewedCommand (level + 1)) block.Contents
                                  |> String.concat (lnIndent (level + 1)))
        + lnIndent level + "}"

/// Pretty-prints methods.
let printMethod meth =
    "method " + meth.Name
              + " " + printArgList id meth.Params
              + " " + printBlock 0 meth.Body

/// Pretty-prints a variable type.
let printType t =
    match t with
    | Int  -> "int"
    | Bool -> "bool"

/// Pretty-prints a view prototype.
let printViewProto vp =
    "view "
    + vp.VPName
    + printArgList (function | (t, v) -> printType t + " " + v)
                   vp.VPPars
    + ";"

/// Pretty-prints a script variable of the given class.
let printScriptVar cls t v =
    cls + " " + printType t + " " + v + ";"

/// Pretty-prints script lines.
let printScriptLine sl =
    match sl with
    | SGlobal (t, v) -> printScriptVar "global" t v
    | SLocal (t, v) -> printScriptVar "local" t v
    | SMethod m -> printMethod m
    | SViewProto v -> printViewProto v
    | SConstraint c -> printConstraint c

/// Pretty-prints scripts.
let printScript = List.map printScriptLine >> String.concat "\n\n"


