/// Pretty-printing for error messages.
module Starling.Pretty.Errors

open Starling.Errors.Modeller
open Starling.Errors.Var
open Starling.Pretty.Types
open Starling.Pretty.Misc
open Starling.Pretty.AST

/// Pretty-prints variable conversion errors.
let printVarMapError ve =
    match ve with
    | VMEDuplicate vn -> fmt "variable '{0}' is defined multiple times" [vn]
    | VMENotFound vn -> fmt "variable '{0}' not in environment" [vn]

/// Pretty-prints expression conversion errors.
let printExprError ee =
    match ee with
    | EEBadAST (ast, reason) ->
        colonSep [fmt "cannot convert {0} to Z3" [ast |> printExpression]
                  reason |> String]
    | EEVar (ast, vme) ->
        colonSep [fmt "bad variable usage in {0}" [ast |> printExpression]
                  printVarMapError vme]
    | EEVarNotBoolean lv ->
        fmt "lvalue '{0}' is not a suitable type for use in a boolean expression"
            [printLValue lv |> String]
    | EEVarNotArith lv ->
        fmt "lvalue '{0}' is not a suitable type for use in an arithmetic expression"
            [printLValue lv |> String]

/// Pretty-prints view conversion errors.
let printViewError ve =
    match ve with
    | VEBadExpr (view, ee) ->
        colonSep [fmt "bad expression in '{0}'" [printView view]
                  printExprError ee]
    | VEUnsupported (view, reason) ->
        colonSep [fmt "view '{0}' not supported" [printView view]
                  reason |> String]

/// Pretty-prints viewdef conversion errors.
let printViewDefError ve =
    match ve with
    | VDENoSuchView name ->
        fmt "no view prototype for '{0}'" [name]
    | VDEBadParamCount (name, expected, actual) ->
        let exps = sprintf "%d" expected
        let acts = sprintf "%d" actual
        fmt "view '{0}' expects '{1}' params, but was given '{2}'"
            [name
             exps
             acts]
    | VDEBadVars vme ->
        colonSep ["view variable inconsistency" |> String
                  printVarMapError vme]
    | VDEGlobalVarConflict vme ->
        colonSep ["view variables conflict with globals" |> String
                  printVarMapError vme]

/// Pretty-prints constraint conversion errors.
let printConstraintError ce =
    match ce with
    | CEView ve -> printViewDefError ve
    | CEExpr ee -> printExprError ee

/// Pretty-prints axiom errors.
let printAxiomError ae =
    match ae with
    | AEBadGlobal le ->
        colonSep ["error resolving global" |> String
                  printVarMapError le]
    | AEBadLocal le ->
        colonSep ["error resolving local" |> String
                  printVarMapError le]
    | AEBadExpr ee ->
        colonSep ["bad expression in axiom" |> String
                  printExprError ee]
    | AEBadView ve ->
        colonSep ["bad view in axiom" |> String
                  printViewError ve]
    | AETypeMismatch (expected, badvar, got) ->
        fmt "lvalue '{0}' is of type {1}, but should be a {2}"
            [printLValue badvar |> String
             printType got |> String
             printType expected |> String]
    | AEUnsupportedAtomic (atom, reason) ->
        colonSep [fmt "cannot use {0} in an axiom: "
                      [printAtomicAction atom]
                  reason |> String]
    | AEUnsupportedCommand (cmd, reason) ->
        colonSep [fmt "cannot use {0} in an axiom: "
                      [printCommand 0 cmd]
                  reason |> String]

/// Pretty-prints view prototype conversion errors
let printViewProtoError vpe =
    match vpe with
    | VPEDuplicateParam (vp, param) ->
        fmt "view proto '{0} has duplicate param {1}"
            [printViewProto vp
             param]

/// Pretty-prints model conversion errors.
let printModelError ce =
    match ce with
    | MEConstraint ce -> printConstraintError ce
    | MEVar ve -> printVarMapError ve
    | MEAxiom ae -> printAxiomError ae
    | MEVProto vpe -> printViewProtoError vpe
