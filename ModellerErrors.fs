/// Types for Chessie error messages reported by the modeller.
module Starling.Errors.Modeller

open Starling

// TODO(CaptainHayashi): more consistent constructor names

/// Represents an error when converting an expression.
type ExprError =
    | EEBadAST of ast: AST.Expression * reason: string
    ///
/// Represents an error when converting a view.
type ViewError =
    | VEBadExpr of AST.View * ExprError
    | VEUnsupported of AST.View * reason: string

/// Represents an error when converting a constraint.
type ConstraintError =
    | CEView of ViewError
    | CEExpr of ExprError

/// Represents an error when converting a variable list.
type VarError =
    | VEDuplicate of string

/// Type of errors found when looking up variables.
type LookupError =
    | LENotFound of string
    // TODO(CaptainHayashi): this error exists because we don't implement
    //                       pointers.
    | LEBadLValue of AST.LValue

/// Type of errors found when generating axioms.
type AxiomError =
    | AEBadGlobal of LookupError
    | AEBadLocal of LookupError
    | AEBadExpr of ExprError
    | AEBadView of ViewError
    | AETypeMismatch of expected: AST.Type * badvar: AST.LValue * got: AST.Type
    | AEUnsupportedAtomic of atom: AST.AtomicAction * reason: string
    | AEUnsupportedCommand of cmd: AST.Command * reason: string

/// Represents an error when converting a model.
type ModelError =
    | MEConstraint of ConstraintError
    | MEVar of VarError
    | MEAxiom of AxiomError
