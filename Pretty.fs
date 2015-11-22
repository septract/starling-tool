module Starling.Pretty.Misc

open Starling
open Starling.AST
open Starling.Collator
open Starling.Model
open Starling.Modeller
open Starling.Errors.Modeller
open Starling.Pretty.AST

/// Pretty-prints a collated script.
let printCollatedScript cs =
    String.concat "\n\n" [
        String.concat "\n" <| List.map printViewProto cs.CVProtos
        String.concat "\n" <| List.map (uncurry (printScriptVar "global")) cs.CGlobals
        String.concat "\n" <| List.map (uncurry (printScriptVar "local")) cs.CLocals
        String.concat "\n" <| List.map printConstraint cs.CConstraints
        String.concat "\n\n" <| List.map printMethod cs.CMethods ]

/// Pretty-prints expression conversion errors.
let printExprError ee =
    match ee with
    | EEBadAST (ast, reason) ->
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
    name + ": " + (match var with
                   | IntVar  tv -> "int " + printTVar tv
                   | BoolVar tv -> "bool " + printTVar tv)

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
                 + printInConditionPair outer (lnIndent (level + 1)
                                               + "begin block"
                                               + lnIndent (level + 1)
                                               + String.concat (lnIndent (level + 1))
                                                               (List.map (printPartAxiom (level + 1)) inner)
                                               + lnIndent (level + 1) 
                                               + "end block"
                                               + lnIndent level)
                       + lnIndent level + "end"
    | PAITE (expr, outer, inTrue, inFalse) ->
        "begin if " + (expr.ToString ())
                    + lnIndent level
                    + printInConditionPair outer (lnIndent (level + 1)
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
                                                  + lnIndent level)
                    + lnIndent level + "end"

/// Pretty-prints a model constraint.
let printModelConstraint c =
    "    View: " + printModelViews (c.CViews)
    + "\n"
    + "      Z3: " + c.CZ3.ToString ()


/// Pretty-prints a model.
let printModel model =
    "Globals: \n    "
    + String.concat "\n    "
                    (List.map printModelVar (Map.toList model.Globals))
    + "\n\n"
    + "Locals: \n    "
    + String.concat "\n    "
                    (List.map printModelVar (Map.toList model.Locals))
    + "\n\n"
    + "Constraints: \n"
    + String.concat "\n"
                    (List.map printModelConstraint model.DefViews)
    + "\n\n"
    + "Axioms:"
    + lnIndent 1
    + String.concat (lnIndent 1)
                    (List.map (printPartAxiom 1) model.Axioms)
