module Starling.Pretty.Lang.AST

open Starling.Collections
open Starling.Var
open Starling.Lang.AST
open Starling.Pretty.Types

/// Pretty-prints lvalues.
let rec printLValue = function 
    | LVIdent i -> String i

/// Pretty-prints Boolean operations.
let printBop = 
    function 
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
    >> String

/// Pretty-prints expressions.
/// This is not guaranteed to produce an optimal expression.
let rec printExpression = 
    function 
    | True -> String "true"
    | False -> String "false"
    | Int i -> i.ToString() |> String
    | LV x -> printLValue x
    | Bop(op, a, b) -> 
        hsep [ printExpression a
               printBop op
               printExpression b ]
        |> parened

/// Pretty-prints views.
let rec printView = 
    function 
    | Func f -> printFunc printExpression f
    | Unit -> String "emp"
    | Join(l, r) -> binop "*" (printView l) (printView r)
    | IfView(e, l, r) -> 
        hsep [ String "if"
               printExpression e
               String "then"
               printView l
               String "else"
               printView r ]

/// Pretty-prints view definitions.
let rec printViewDef = 
    function 
    | ViewDef.Func f -> printFunc String f
    | ViewDef.Unit -> String "emp"
    | ViewDef.Join(l, r) -> binop "*" (printViewDef l) (printViewDef r)

/// Pretty-prints view lines.
let printViewLine vl = 
    vl
    |> printView
    |> ssurround "{|" "|}"

/// Pretty-prints constraints.
let printConstraint { CView = v; CExpression = e } = 
    hsep [ String "constraint"
           printViewDef v
           String "->"
           printExpression e ]
    |> withSemi

/// Pretty-prints fetch modes.
let printFetchMode = 
    function 
    | Direct -> Nop
    | Increment -> String "++"
    | Decrement -> String "--"

/// Pretty-prints atomic actions.
let printAtomicAction = 
    function 
    | CompareAndSwap(l, f, t) -> 
        func "CAS" [ printLValue l
                     printLValue f
                     printExpression t ]
    | Fetch(l, r, m) -> 
        equality (printLValue l) (hjoin [ printExpression r
                                          printFetchMode m ])
    | Postfix(l, m) -> 
        hjoin [ printLValue l
                printFetchMode m ]
    | Id -> String "id"
    | Assume e -> func "assume" [ printExpression e ]

/// Pretty-prints commands with the given indent level (in spaces).
let rec printCommand = 
    function 
    | Atomic a -> 
        a
        |> printAtomicAction
        |> angled
    | Skip -> Nop |> withSemi
    | If(c, t, f) -> 
        hsep [ "if" |> String
               c
               |> printExpression
               |> parened
               t |> printBlock
               f |> printBlock ]
    | While(c, b) -> 
        hsep [ "while" |> String
               c
               |> printExpression
               |> parened
               b |> printBlock ]
    | DoWhile(b, c) -> 
        hsep [ "do" |> String
               b |> printBlock
               "while" |> String
               c
               |> printExpression
               |> parened ]
        |> withSemi
    | Blocks bs -> 
        bs
        |> List.map printBlock
        |> hsepStr "||"
    | Assign(l, r) -> binop "=" (printLValue l) (printExpression r) |> withSemi

/// Pretty-prints viewed commands with the given indent level (in spaces).
and printViewedCommand { Command = c; Post = p } = 
    vsep [ printCommand c
           printViewLine p ]

/// Pretty-prints blocks with the given indent level (in spaces).
and printBlock { Pre = p; Contents = c } = 
    vsep ((p
           |> printViewLine
           |> Indent)
          :: List.map (printViewedCommand >> Indent) c)
    |> braced

/// Pretty-prints methods.
let printMethod { Signature = s; Body = b } = 
    hsep [ "method" |> String
           printFunc String s
           b |> printBlock ]

/// Pretty-prints a variable type.
let printType = 
    function 
    | Type.Int -> "int" |> String
    | Type.Bool -> "bool" |> String

/// Pretty-prints a view prototype.
let printViewProto { ViewProto.Name = n; Params = ps } = 
    hsep [ "view" |> String
           func n (List.map (fun (t, v) -> 
                       hsep [ t |> printType
                              v |> String ]) ps) ]
    |> withSemi

/// Pretty-prints a script variable of the given class.
let printScriptVar cls t v = 
    hsep [ String cls
           printType t
           String v ]
    |> withSemi

/// Pretty-prints script lines.
let printScriptLine = 
    function 
    | Global(t, v) -> printScriptVar "global" t v
    | Local(t, v) -> printScriptVar "local" t v
    | Method m -> printMethod m
    | ViewProto v -> printViewProto v
    | Constraint c -> printConstraint c

/// Pretty-prints scripts.
let printScript = List.map printScriptLine >> fun ls -> VSep(ls, vsep [ Nop; Nop ])
