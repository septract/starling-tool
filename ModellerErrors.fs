/// Types for Chessie error messages reported by the modeller.
module Starling.Errors.Modeller

open Starling
open Starling.Errors.Var

// TODO(CaptainHayashi): more consistent constructor names

/// Represents an error when converting an expression.
type ExprError =
    | EEBadAST of ast: AST.Expression * reason: string

/// Represents an error when converting a view prototype.
type ViewProtoError =
    | VPEDuplicateParam of AST.ViewProto * param: string

/// Represents an error when converting a view.
type ViewError =
    | VEBadExpr of AST.View * ExprError
    | VEUnsupported of AST.View * reason: string

/// Represents an error when converting a view definition.
type ViewDefError =
      // A viewdef referred to a view with no known name.
    | VDENoSuchView of name: string
      // A viewdef referred to a view with the wrong number of params.
    | VDEBadParamCount of name: string * expected: int * actual: int
      // A viewdef used variables in incorrect ways, eg by duplicating.
    | VDEBadVars of VarMapError
      // A viewdef conflicted with the global variables.
    | VDEGlobalVarConflict of VarMapError

/// Represents an error when converting a constraint.
type ConstraintError =
    | CEView of ViewDefError
    | CEExpr of ExprError

/// Type of errors found when generating axioms.
type AxiomError =
    | AEBadGlobal of VarMapError
    | AEBadLocal of VarMapError
    | AEBadExpr of ExprError
    | AEBadView of ViewError
    | AETypeMismatch of expected: Var.Type * badvar: Var.LValue * got: Var.Type
    | AEUnsupportedAtomic of atom: AST.AtomicAction * reason: string
    | AEUnsupportedCommand of cmd: AST.Command * reason: string

/// Represents an error when converting a model.
type ModelError =
    | MEVProto of ViewProtoError
    | MEConstraint of ConstraintError
    | MEAxiom of AxiomError
    | MEVar of VarMapError
