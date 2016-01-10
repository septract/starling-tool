/// Pretty-printing for error messages.
module Starling.Pretty.Errors

open Starling.Errors.Lang.Modeller
open Starling.Errors.Var
open Starling.Errors.Z3.Translator
open Starling.Pretty.Types
open Starling.Pretty.Misc
open Starling.Pretty.Lang.AST

/// Formats an error that is wrapping another error.
let wrapped wholeDesc whole err = headed (sprintf "In %s '%s'" wholeDesc (print whole)) [ err ]

/// Pretty-prints variable conversion errors.
let printVarMapError =
    function
    | Duplicate vn -> fmt "variable '{0}' is defined multiple times" [ vn ]
    | NotFound vn -> fmt "variable '{0}' not in environment" [ vn ]

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
    | VDENoSuchView name -> fmt "no view prototype for '{0}'" [ name ]
    | VDEBadParamCount(name, expected, actual) ->
        fmt "view '{0}' expects '{1}' params, but was given '{2}'" [ name; expected; actual ]
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
        colonSep [ fmt "cannot use {0} in an axiom: " [ printAtomicAction atom ]
                   reason |> String ]
    | AEUnsupportedCommand(cmd, reason) ->
        colonSep [ fmt "cannot use {0} in an axiom: " [ printCommand cmd ]
                   reason |> String ]

/// Pretty-prints view prototype conversion errors
let printViewProtoError = function
    | VPEDuplicateParam(vp, param) ->
        fmt "view proto '{0} has duplicate param {1}" [ printViewProto vp
                                                        param ]

/// Pretty-prints model conversion errors.
let printModelError =
    function
    | MEConstraint(constr, err) -> wrapped "constraint" (constr |> printViewDef) (err |> printConstraintError)
    | MEVar err ->
        colonSep [ "invalid variable declarations" |> String
                   err |> printVarMapError ]
    | MEAxiom(methname, err) -> wrapped "method" (methname |> String) (err |> printAxiomError)
    | MEVProto(vproto, err) -> wrapped "view prototype" (vproto |> printViewProto) (err |> printViewProtoError)

/// Pretty-prints Z3 translation errors.
let printZ3TranslatorError =
    function
    | IndefiniteConstraint vd ->
        fmt "constraint of '{0}' is indefinite ('?'), and Z3 cannot use it" [ printModelViewDefs vd ]
