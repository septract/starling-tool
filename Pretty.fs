module Starling.Pretty

open Starling.AST
open Starling.Collator
open Starling.Model
open Starling.Modeller
open Starling.Errors.Modeller

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
let printArgList argp ss = "(" + String.concat ", " ( List.map argp ss ) + ")"

/// Pretty-prints views.
let rec printView v =
    match v with
        | Func      ( vv,  xs ) -> vv + printArgList printExpression xs
        | Unit                  -> "emp"
        | Join      ( l, r )    -> printView l + " * " + printView r
        | IfView    ( e, l, r ) -> "if " + printExpression e + " then " + printView l + " else " + printView r

/// Pretty-prints view definitions.
let rec printViewDef v =
    match v with
        | DFunc      ( vv,  xs ) -> vv + printArgList id xs
        | DUnit                  -> "emp"
        | DJoin      ( l, r )    -> printViewDef l + " * " + printViewDef r

/// Pretty-prints view lines.
let printViewLine vl = "{| " + printView vl + " |}"

/// Pretty-prints constraints.
let printConstraint cs =
    "constraint " + printViewDef cs.CView + " => " + printExpression cs.CExpression + ";"

/// Pretty-prints fetch modes.
let printFetchMode m =
    match m with
        | Direct    -> ""
        | Increment -> "++"
        | Decrement -> "--"

/// Pretty-prints atomic actions.
let printAtomicAction atom =
    match atom with
        | CompareAndSwap ( l, f, t ) -> "CAS(" + printLValue l + ", " + printLValue f + ", " + printExpression t
        | Fetch          ( l, r, m ) -> printLValue l + " = " + printLValue r + printFetchMode m
        | Postfix        ( l, m )    -> printLValue l + printFetchMode m
        | Id                         -> "id"
        | Assume         e           -> "assume(" + printExpression e + ")"

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
        + printArgList ( fun tv -> printType ( fst tv ) + " " + snd tv )
                       vp.VPPars
        + ";"

/// Pretty-prints a script variable of the given class.
let printScriptVar cls t v =
    cls + " " + printType t + " " + v + ";"

/// Pretty-prints script lines.
let printScriptLine sl =
    match sl with
        | SGlobal     ( t, v ) -> printScriptVar "global" t v
        | SLocal      ( t, v ) -> printScriptVar "local" t v
        | SMethod     m        -> printMethod m
        | SViewProto  v        -> printViewProto v
        | SConstraint c        -> printConstraint c

/// Pretty-prints scripts.
let printScript = List.map printScriptLine >> String.concat "\n\n"

/// Pretty-prints a collated script.
let printCollatedScript cs =
    String.concat "\n\n" [
        String.concat "\n"   <| List.map printViewProto                          cs.CVProtos
        String.concat "\n"   <| List.map ( uncurry ( printScriptVar "global" ) ) cs.CGlobals
        String.concat "\n"   <| List.map ( uncurry ( printScriptVar "local"  ) ) cs.CLocals
        String.concat "\n"   <| List.map printConstraint                         cs.CConstraints
        String.concat "\n\n" <| List.map printMethod                             cs.CMethods
    ]

/// Pretty-prints expression conversion errors.
let printExprError ee =
    match ee with
        | EEBadAST ( ast, reason ) ->
            "cannot convert " + printExpression ast
                              + " to Z3: " + reason

/// Pretty-prints view conversion errors.
let printViewError ve =
    match ve with
    | VEBadExpr (view, ee) ->
        "bad expression in '" + printView view
                      + "': " + printExprError ee
    | VEUnsupported (view, reason) ->
        "view '" + printView view + "' not supported: " + reason

/// Pretty-prints constraint conversion errors.
let printConstraintError ce =
    match ce with
        | CEView ve -> printViewError ve
        | CEExpr ee -> printExprError ee

/// Pretty-prints variable conversion errors.
let printVarError ve =
    match ve with
        | VEDuplicate vn -> "variable '" + vn + "' is defined multiple times"

/// Pretty-prints lookup errors.
let printLookupError le =
    match le with
    | LENotFound s -> "variable " + s + " referenced but not declared"
    | LEBadLValue l -> "FIXME: " + printLValue l + " is not a variable and is unsupported"

/// Pretty-prints axiom errors.
let printAxiomError ae =
    match ae with
    | AEBadGlobal le -> "error resolving global: " + printLookupError le
    | AEBadLocal le -> "error resolving local: " + printLookupError le
    | AEBadExpr ee -> "bad expression in axiom: " + printExprError ee
    | AEBadView ve -> "bad view in axiom: " + printViewError ve
    | AETypeMismatch (expected, badvar, got) ->
        "type error: " + printLValue badvar
                       + " is of type " + printType got
                       + ", but should be of type " + printType expected
    | AEUnsupportedAtomic (atom, reason) ->
        "cannot use " + printAtomicAction atom
                      + " in an axiom: " + reason
    | AEUnsupportedCommand (cmd, reason) ->
        "cannot use " + printCommand 0 cmd
                      + " in an axiom: " + reason

/// Pretty-prints model conversion errors.
let printModelError ce =
    match ce with
        | MEConstraint ce -> printConstraintError ce
        | MEVar ve -> printVarError ve
        | MEAxiom ae -> printAxiomError ae

/// Pretty-prints a flat view.
let printModelView v =
    // TODO(CaptainHayashi): sort pretty-printing out so this can move
    v.VName + "(" + String.concat ", " v.VParams + ")"

/// Pretty-prints a multiset of views.
let printModelViews vs =
    "[" + String.concat ", " ( List.map printModelView vs ) + "]"

/// Pretty-prints TVars.
let printTVar tvar =
    "(Z3: " + tvar.VarExpr.ToString () + ", "
            + tvar.VarPreExpr.ToString () + ", "
            + tvar.VarPostExpr.ToString () + ", "
            + tvar.VarFrameExpr.ToString () + ")"

/// Pretty-prints model variables.
let printModelVar nvar =
    let name, var = nvar
    name + ": " + (
        match var with
            | IntVar  tv -> "int " + printTVar tv
            | BoolVar tv -> "bool " + printTVar tv
    )

/// Pretty-prints a conditional view.
let rec printCondView cv =
    match cv with
    | CITEView (i, t, e) -> "if " + (i.ToString ())
                                  + " then " + printCondViewList t
                                  + " else " + printCondViewList e
    | CSetView v -> printModelView v

/// Pretty-prints a list of cond-views.
and printCondViewList cvs =
    "[| " + (List.map printCondView cvs |> String.concat "; ") + " |]"


/// Pretty-prints something wrapped in a condition pair.
let printInConditionPair cpair inner =
   printCondViewList cpair.Pre
   + inner
   + printCondViewList cpair.Post
    
/// Lifts a pretty-printer to optional values.
let printOption pp ov =
    match ov with
    | None -> "(none)"
    | Some v -> pp v

/// Pretty-prints a fetch prim.
let printFetchPrim ty dest src mode =
    "fetch<" + ty + "> {"
    + printOption printLValue dest
    + " = "
    + printLValue src
    + printFetchMode mode
    + "}"

/// Pretty-prints a CAS prim.
let printCASPrim ty dest src set =
    "cas<" + ty + "> {"
    + printLValue dest
    + " = "
    + printLValue src
    + (set.ToString ())
    + "}"

/// Pretty-prints a local-set prim.
let printLocalPrim ty dest src =
    "lset<" + ty + "> {"
    + printLValue dest
    + " = "
    + (src.ToString ())
    + "}"

/// Pretty-prints a prim.
let printPrim prim =
    match prim with
    | ArithFetch (dest, src, mode) -> printFetchPrim "arith" dest src mode
    | BoolFetch (dest, src) -> printFetchPrim "bool" dest src Direct
    | ArithCAS (dest, src, set) -> printCASPrim "arith" dest src set
    | BoolCAS (dest, src, set) -> printCASPrim "bool" dest src set
    | ArithLocalSet (dest, src) -> printLocalPrim "arith" dest src
    | BoolLocalSet (dest, src) -> printLocalPrim "bool" dest src
    | PrimId -> "id"
    | PrimAssume expr -> "assume {" + (expr.ToString ()) + "}"

/// Pretty-prints a model axiom.
let printModelAxiom axiom =
    printInConditionPair axiom.AConditions (" <" + String.concat "; " ( List.map printPrim axiom.ACommand ) + "> ")

/// Pretty-prints a part-axiom at the given indent level.
let rec printPartAxiom level axiom =
    match axiom with
    | PAAxiom ax -> printModelAxiom ax
    | PAWhile (isDo, expr, outer, inner) ->
        "begin " + (if isDo then "do-while" else "while")
                 + " " + (expr.ToString ())
                 + lnIndent level
                 + printInConditionPair outer ( lnIndent (level + 1)
                                                + "begin block"
                                                + lnIndent (level + 1)
                                                + String.concat (lnIndent (level + 1))
                                                                (List.map (printPartAxiom (level + 1)) inner)
                                                + lnIndent (level + 1) 
                                                + "end block"
                                                + lnIndent level )
                       + lnIndent level + "end"
    | PAITE (expr, outer, inTrue, inFalse) ->
        "begin if " + (expr.ToString ())
                    + lnIndent level
                    + printInConditionPair outer ( lnIndent (level + 1)
                                                   + "begin true"
                                                   + lnIndent (level + 1)
                                                   + String.concat (lnIndent (level + 1))
                                                                   (List.map (printPartAxiom (level + 1)) inTrue)
                                                   + lnIndent (level + 1)
                                                   + "end true; begin false"
                                                   + lnIndent (level + 1)
                                                   + String.concat (lnIndent (level + 1))
                                                                   (List.map (printPartAxiom (level + 1)) inFalse)
                                                   + lnIndent (level + 1)
                                                   + "end false"
                                                   + lnIndent level )
                    + lnIndent level + "end"

/// Pretty-prints a model.
let printModel model =
    "Globals: \n    " + String.concat "\n    " (
        List.map printModelVar ( Map.toList model.Globals )
    ) + "\n\n" +
    "Locals: \n    " + String.concat "\n    " (
        List.map printModelVar ( Map.toList model.Locals )
    ) + "\n\n" +
    "Constraints: \n" + String.concat "\n" (
        List.map (
            fun c ->
                "    View: " + printModelViews ( c.CViews )
                           + "\n"
                           + "      Z3: " + c.CZ3.ToString ()
         ) model.DefViews
    ) + "\n\n" +
    "Axioms:" + lnIndent 1 + String.concat (lnIndent 1) (
        List.map (printPartAxiom 1) model.Axioms )
