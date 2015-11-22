module Starling.Pretty.Misc

open Starling
open Starling.AST
open Starling.Collator
open Starling.Model
open Starling.Modeller
open Starling.Errors.Modeller
open Starling.Pretty.AST
open Starling.Pretty.Types

/// Pretty-prints a collated script.
let printCollatedScript cs =
    VSep ([ vsep <| List.map (printViewProto >> String) cs.CVProtos
            vsep <| List.map (uncurry (printScriptVar "global") >> String) cs.CGlobals
            vsep <| List.map (uncurry (printScriptVar "local") >> String) cs.CLocals
            vsep <| List.map (printConstraint >> String) cs.CConstraints
            VSep (List.map (printMethod >> String) cs.CMethods, Separator) ],
          Separator)

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
    hsep [ String v.VName
           parened (HSep (List.map String v.VParams, String ",")) ]

/// Pretty-prints a multiset of views.
let printModelViews vs =
    squared (HSep (List.map printModelView vs, String ","))

/// Pretty-prints Z3 expressions
let printZ3Exp expr = String (expr.ToString ())

/// Pretty-prints TVars.
let printTVar tvar =
    ssurround "(Z3:"
              ")"
              (HSep ( [ printZ3Exp tvar.VarExpr
                        printZ3Exp tvar.VarPreExpr
                        printZ3Exp tvar.VarPostExpr
                        printZ3Exp tvar.VarFrameExpr ], String ","))

/// Pretty-prints model variables.
let printModelVar nvar =
    let name, var = nvar
    HSep ( [ String name
             (match var with
              | IntVar tv -> hsep [ String "int"
                                    printTVar tv ]
              | BoolVar tv -> hsep [ String "bool"
                                     printTVar tv ] ) ],
           String ":")

/// Pretty-prints a conditional view.
let rec printCondView cv =
    match cv with
    | CITEView (i, t, e) ->
        hsep [ String "if"
               printZ3Exp i
               String "then"
               printCondViewList t
               String "else"
               printCondViewList e ]
    | CSetView v -> printModelView v

/// Pretty-prints a list of cond-views.
and printCondViewList cvs =
    ssurround "[| "
              " |]"
              (HSep (List.map printCondView cvs, String ";"))


/// Pretty-prints something wrapped in a condition pair.
let printInConditionPair cpair inner =
    Surround (hsep [ printCondViewList cpair.Pre ; Nop ],
              inner,
              hsep [ Nop ; printCondViewList cpair.Post ])
    
/// Lifts a pretty-printer to optional values.
let printOption pp ov =
    match ov with
    | None -> String "(none)"
    | Some v -> pp v

/// Pretty-prints a fetch prim.
let printFetchPrim ty dest src mode =
    hsep [ String ("fetch<" + ty + ">")
           parened (hsep [ printOption (printLValue >> String) dest
                           String "="
                           String (printLValue src)
                           String (printFetchMode mode) ] ) ]

/// Pretty-prints a CAS prim.
let printCASPrim ty dest src set =
    hsep [ String ("cas<" + ty + ">")
           parened (HSep ( [ String (printLValue dest)
                             String (printLValue src)
                             String (set.ToString ()) ],
                           String ",")) ]

/// Pretty-prints a local-set prim.
let printLocalPrim ty dest src =
    hsep [ String ("lset<" + ty + ">")
           parened (hsep [ String (printLValue dest)
                           String "="
                           String (src.ToString ()) ] ) ]

/// Pretty-prints a prim.
let printPrim prim =
    match prim with
    | ArithFetch (dest, src, mode) -> printFetchPrim "arith" dest src mode
    | BoolFetch (dest, src) -> printFetchPrim "bool" dest src Direct
    | ArithCAS (dest, src, set) -> printCASPrim "arith" dest src set
    | BoolCAS (dest, src, set) -> printCASPrim "bool" dest src set
    | ArithLocalSet (dest, src) -> printLocalPrim "arith" dest src
    | BoolLocalSet (dest, src) -> printLocalPrim "bool" dest src
    | PrimId -> String "id"
    | PrimAssume expr -> hsep [ String "assume"
                                braced (String (expr.ToString ())) ]

/// Pretty-prints a model axiom.
let printModelAxiom axiom =
    printInConditionPair axiom.AConditions
                         (angled (HSep (List.map printPrim axiom.ACommand, String ";")))

/// Pretty-prints a part-axiom at the given indent level.
let rec printPartAxiom axiom =
    match axiom with
    | PAAxiom ax -> printModelAxiom ax
    | PAWhile (isDo, expr, outer, inner) ->
        vsep [ hsep [ String "begin"
                      String (if isDo then "do-while" else "while")
                      String (expr.ToString ()) ]
               printInConditionPair outer
                                    (vsep [ String "begin block"
                                            ivsep <| List.map printPartAxiom inner
                                            String "end block" ] )
               String "end" ]
    | PAITE (expr, outer, inTrue, inFalse) ->
        vsep [ hsep [ String "begin if"
                      String (expr.ToString ()) ]
               printInConditionPair outer
                                    (vsep [ String "begin true"
                                            ivsep <| List.map printPartAxiom inTrue
                                            String "end true; begin false"
                                            ivsep <| List.map printPartAxiom inFalse
                                            String "end false" ] )
               String "end" ]

/// Pretty-prints a model constraint.
let printModelConstraint c =
    keyMap [ ("View", printModelViews (c.CViews))
             ("Z3", c.CZ3.ToString () |> String) ]

/// Pretty-prints a model.
let printModel model =
    headed "Model"
           [ headed "Globals" <| List.map printModelVar (Map.toList model.Globals)
             Separator
             headed "Locals" <| List.map printModelVar (Map.toList model.Locals)
             Separator
             headed "Constraints"  <| List.map printModelConstraint model.DefViews
             Separator
             headed "Axioms" <| List.map printPartAxiom model.Axioms ]
