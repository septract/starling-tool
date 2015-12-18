module Starling.Pretty.Lang.AST

open Starling.Var
open Starling.Lang.AST
open Starling.Pretty.Types

/// Pretty-prints lvalues.
let rec printLValue =
    function | LVIdent i -> i

/// Pretty-prints Boolean operations.
let printBop =
    function | Mul -> "*"
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
let rec printExpression =
    function | TrueExp -> "true"
             | FalseExp -> "false"
             | IntExp i -> i.ToString ()
             | LVExp x -> printLValue x
             | BopExp (op, a, b) ->
                   "(" + printExpression a + " " + printBop op + " " + printExpression b + ")"

/// Pretty-prints argument lists.
let printArgList argp ss = "(" + String.concat ", " ( List.map argp ss ) + ")"

/// Pretty-prints views.
let rec printView =
    function | Func (vv, xs) -> vv + printArgList printExpression xs
             | Unit -> "emp"
             | Join (l, r) -> printView l + " * " + printView r
             | IfView (e, l, r) -> "if " + printExpression e + " then " + printView l + " else " + printView r

/// Pretty-prints view definitions.
let rec printViewDef =
    function | DFunc (vv, xs) -> vv + printArgList id xs
             | DUnit -> "emp"
             | DJoin (l, r) -> printViewDef l + " * " + printViewDef r

/// Pretty-prints view lines.
let printViewLine vl = "{| " + printView vl + " |}"

/// Pretty-prints constraints.
let printConstraint {CView = v; CExpression = e} =
    "constraint " + printViewDef v + " => " + printExpression e + ";"

/// Pretty-prints fetch modes.
let printFetchMode =
    function | Direct -> ""
             | Increment -> "++"
             | Decrement -> "--"

/// Pretty-prints atomic actions.
let printAtomicAction =
    function | CompareAndSwap (l, f, t) ->
                   "CAS(" + printLValue l + ", " + printLValue f + ", " + printExpression t
             | Fetch (l, r, m) -> printLValue l + " = " + printExpression r + printFetchMode m
             | Postfix (l, m) -> printLValue l + printFetchMode m
             | Id -> "id"
             | Assume e -> "assume(" + printExpression e + ")"

/// Pretty-prints commands with the given indent level (in spaces).
let rec printCommand level =
    function | Atomic a -> "<" + printAtomicAction a + ">;"
             | Skip -> ";"
             | If (c, t, f) -> "if (" + printExpression c + ") " + printBlock level t + " " + printBlock level f
             | While (c, b) -> "while (" + printExpression c + ") " + printBlock level b
             | DoWhile (b, c) -> "do " + printBlock level b + " while (" + printExpression c + ");"
             | Blocks bs -> List.map (printBlock level) bs |> String.concat " || "
             | Assign (l, r) -> printLValue l + " = " + printExpression r + ";"
/// Pretty-prints viewed commands with the given indent level (in spaces).
and printViewedCommand level {Command = c ; Post = p} =
    printCommand level c + lnIndent level + printViewLine p
/// Pretty-prints blocks with the given indent level (in spaces).
and printBlock level {Pre = p; Contents = c} =
    "{" + lnIndent (level + 1) + printViewLine p
        + lnIndent (level + 1) + (List.map (printViewedCommand (level + 1)) c
                                  |> String.concat (lnIndent (level + 1)))
        + lnIndent level + "}"

/// Pretty-prints methods.
let printMethod {Name = n ; Params = ps ; Body = b} =
    "method " + n
              + " " + printArgList id ps
              + " " + printBlock 0 b

/// Pretty-prints a variable type.
let printType =
    function | Int  -> "int"
             | Bool -> "bool"

/// Pretty-prints a view prototype.
let printViewProto {VPName = n ; VPPars = ps} =
    "view "
    + n
    + printArgList (function | (t, v) -> printType t + " " + v)
                   ps
    + ";"

/// Pretty-prints a script variable of the given class.
let printScriptVar cls t v =
    cls + " " + printType t + " " + v + ";"

/// Pretty-prints script lines.
let printScriptLine =
    function | SGlobal (t, v) -> printScriptVar "global" t v
             | SLocal (t, v) -> printScriptVar "local" t v
             | SMethod m -> printMethod m
             | SViewProto v -> printViewProto v
             | SConstraint c -> printConstraint c

/// Pretty-prints scripts.
let printScript = List.map printScriptLine >> String.concat "\n\n"


