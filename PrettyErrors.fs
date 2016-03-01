/// Pretty-printing for error messages.
module Starling.Pretty.Errors

open Starling.Instantiate
open Starling.Semantics
open Starling.Errors.Lang.Modeller
open Starling.Errors.Var
open Starling.Var.Pretty
open Starling.Core.Model.Pretty
open Starling.Pretty.Expr
open Starling.Pretty.Types
open Starling.Lang.AST.Pretty

/// Formats an error that is wrapping another error.
let wrapped wholeDesc whole err = headed (sprintf "In %s '%s'" wholeDesc (print whole)) [ err ]

/// Pretty-prints variable conversion errors.
let printVarMapError =
    function
    | Duplicate vn -> fmt "variable '{0}' is defined multiple times" [ String vn ]
    | NotFound vn -> fmt "variable '{0}' not in environment" [ String vn ]

/// Pretty-prints expression conversion errors.
let printExprError =
    function
    | ExprNotBoolean ->
        "expression is not suitable for use in a Boolean position" |> String
    | VarNotBoolean lv ->
        fmt "lvalue '{0}' is not a suitable type for use in a Boolean expression" [ printLValue lv ]
    | ExprNotArith ->
        "expression is not suitable for use in an arithmetic position" |> String
    | VarNotArith lv ->
        fmt "lvalue '{0}' is not a suitable type for use in an arithmetic expression" [ printLValue lv ]
    | Var(var, err) -> wrapped "variable" (var |> printLValue) (err |> printVarMapError)

/// Pretty-prints view conversion errors.
let printViewError = function
    | VEBadExpr(expr, err) -> wrapped "expression" (expr |> printExpression) (err |> printExprError)

/// Pretty-prints viewdef conversion errors.
let printViewDefError =
    function
    | VDENoSuchView name -> fmt "no view prototype for '{0}'" [ String name ]
    | VDEBadParamCount(name, expected, actual) ->
        fmt "view '{0}' expects {1} params, but was given {2}" [ name |> String
                                                                 expected |> sprintf "%d" |> String
                                                                 actual |> sprintf "%d" |> String ]
    | VDEBadVars err ->
        colonSep [ "invalid variable usage" |> String
                   err |> printVarMapError ]
    | VDEGlobalVarConflict err ->
        colonSep [ "parameters conflict with global variables" |> String
                   err |> printVarMapError ]

/// Pretty-prints constraint conversion errors.
let printConstraintError =
    function
    | CEView(vdef, err) -> wrapped "view definition" (vdef |> printViewDef) (err |> printViewDefError)
    | CEExpr(expr, err) -> wrapped "expression" (expr |> printExpression) (err |> printExprError)

/// Pretty-prints axiom errors.
let printAxiomError =
    function
    | AEBadGlobal(var, err) -> wrapped "global variable" (var |> printLValue) (err |> printVarMapError)
    | AEBadLocal(var, err) -> wrapped "local variable" (var |> printLValue) (err |> printVarMapError)
    | AEBadExpr(expr, err) -> wrapped "expression" (expr |> printExpression) (err |> printExprError)
    | AEBadView(view, err) -> wrapped "view" (view |> printView) (err |> printViewError)
    | AETypeMismatch(expected, badvar, got) ->
        fmt "lvalue '{0}' is of type {1}, but should be a {2}" [ printLValue badvar
                                                                 printType got
                                                                 printType expected ]
    | AEUnsupportedAtomic(atom, reason) ->
        colonSep [ fmt "cannot use {0} in an axiom" [ printAtomicAction atom ]
                   reason |> String ]
    | AEUnsupportedCommand(cmd, reason) ->
        colonSep [ fmt "cannot use {0} in an axiom" [ printCommand cmd ]
                   reason |> String ]

/// Pretty-prints view prototype conversion errors
let printViewProtoError = function
    | VPEDuplicateParam(vp, param) ->
        fmt "view proto '{0} has duplicate param {1}" [ printViewProto vp
                                                        String param ]

/// Pretty-prints model conversion errors.
let printModelError =
    function
    | MEConstraint(constr, err) -> wrapped "constraint" (constr |> printViewDef) (err |> printConstraintError)
    | MEVar err ->
        colonSep [ "invalid variable declarations" |> String
                   err |> printVarMapError ]
    | MEAxiom(methname, err) -> wrapped "method" (methname |> String) (err |> printAxiomError)
    | MEVProto(vproto, err) -> wrapped "view prototype" (vproto |> printViewProto) (err |> printViewProtoError)

/// Pretty-prints instantiation errors.
let printInstantiationError =
    function
    | TypeMismatch (par, atype) ->
        fmt "parameter '{0}' conflicts with argument of type '{1}'"
            [ printParam par; printType atype ]
    | CountMismatch (fn, dn) ->
        fmt "view usage has {0} parameter(s), but its definition has {1}"
            [ fn |> sprintf "%d" |> String; dn |> sprintf "%d" |> String ]


/// Pretty-prints semantics errors.
let printSemanticsError =
    function
    | Instantiate (cmd, error) ->
      colonSep
          [ fmt "couldn't instantiate command '{0}'" [ printVFunc cmd ]
            printInstantiationError error ]
    | MissingDef cmd ->
        fmt "command '{0}' has no semantic definition"
            [ printVFunc cmd ]
