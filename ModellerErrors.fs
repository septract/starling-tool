/// Types for Chessie error messages reported by the modeller.
module Starling.Errors.Lang.Modeller

open Starling
open Starling.Lang
open Starling.Errors.Var

// TODO(CaptainHayashi): more consistent constructor names
/// Represents an error when converting an expression.
type ExprError = 
    /// Some unclassified error occurred with the AST.
    | EEBadAST of ast : AST.Expression * reason : string
    /// A variable usage in the expression produced a `VarMapError`.
    | EEVar of ast : AST.Expression * err : VarMapError
    /// A non-Boolean variable was found in a Boolean position.
    | EEVarNotBoolean of var : Var.LValue
    /// A non-arithmetic variable was found in an arithmetic position.
    | EEVarNotArith of var : Var.LValue

/// Represents an error when converting a view prototype.
type ViewProtoError = 
    /// A parameter name was used more than once in the same view prototype.
    | VPEDuplicateParam of AST.ViewProto * param : string

/// Represents an error when converting a view.
type ViewError = 
    /// An expression in the view generated an `ExprError`.
    | VEBadExpr of AST.View * ExprError

/// Represents an error when converting a view definition.
type ViewDefError = 
    /// A viewdef referred to a view with no known name.
    | VDENoSuchView of name : string
    /// A viewdef referred to a view with the wrong number of params.
    | VDEBadParamCount of name : string * expected : int * actual : int
    /// A viewdef used variables in incorrect ways, eg by duplicating.
    | VDEBadVars of VarMapError
    /// A viewdef conflicted with the global variables.
    | VDEGlobalVarConflict of VarMapError

/// Represents an error when converting a constraint.
type ConstraintError = 
    /// The view definition in the constraint generated a `ViewDefError`.
    | CEView of ViewDefError
    /// The expression in the constraint generated an `ExprError`.
    | CEExpr of ExprError

/// Type of errors found when generating axioms.
type AxiomError = 
    /// The axiom uses a variable in global position incorrectly.
    | AEBadGlobal of VarMapError
    /// The axiom uses a variable in local position incorrectly.
    | AEBadLocal of VarMapError
    /// The axiom uses an expression incorrectly.
    | AEBadExpr of ExprError
    /// The axiom uses a view incorrectly.
    | AEBadView of ViewError
    /// The axiom has a type mismatch in lvalue `bad`.
    | AETypeMismatch of expected : Var.Type * bad : Var.LValue * got : Var.Type
    /// The axiom uses a semantically invalid atomic action.
    | AEUnsupportedAtomic of atom : AST.AtomicAction * reason : string
    /// The axiom uses a semantically invalid command.
    | AEUnsupportedCommand of cmd : AST.Command * reason : string

/// Represents an error when converting a model.
type ModelError = 
    /// A view prototype in the program generated a `ViewProtoError`.
    | MEVProto of ViewProtoError
    /// A constraint in the program generated a `ConstraintError`.
    | MEConstraint of ConstraintError
    /// An axiom in the program generated an `AxiomError`.
    | MEAxiom of AxiomError
    /// A variable in the program generated a `VarMapError`.
    | MEVar of VarMapError
