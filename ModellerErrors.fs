/// Types for Chessie error messages reported by the modeller.
module Starling.Errors.Lang.Modeller

open Starling
open Starling.Lang
open Starling.Errors.Var

// TODO(CaptainHayashi): more consistent constructor names
/// Represents an error when converting an expression.
type ExprError = 
    /// A non-Boolean expression was found in a Boolean position.
    | ExprNotBoolean
    /// A non-Boolean variable was found in a Boolean position.
    | VarNotBoolean of var : Var.LValue
    /// A non-arithmetic expression was found in an arithmetic position.
    | ExprNotArith
    /// A non-arithmetic variable was found in an arithmetic position.
    | VarNotArith of var : Var.LValue
    /// A variable usage in the expression produced a `VarMapError`.
    | Var of var : Var.LValue * err : VarMapError

/// Represents an error when converting a view prototype.
type ViewProtoError = 
    /// A parameter name was used more than once in the same view prototype.
    | VPEDuplicateParam of AST.ViewProto * param : string

/// Represents an error when converting a view.
type ViewError = 
    /// An expression in the view generated an `ExprError`.
    | VEBadExpr of expr : AST.Expression * err : ExprError

/// Represents an error when converting a view definition.
type ViewDefError = 
    /// A viewdef referred to a view with no known name.
    | VDENoSuchView of name : string
    /// A viewdef referred to a view with the wrong number of params.
    | VDEBadParamCount of name : string * expected : int * actual : int
    /// A viewdef used variables in incorrect ways, eg by duplicating.
    | VDEBadVars of err : VarMapError
    /// A viewdef conflicted with the global variables.
    | VDEGlobalVarConflict of err : VarMapError

/// Represents an error when converting a constraint.
type ConstraintError = 
    /// The view definition in the constraint generated a `ViewDefError`.
    | CEView of vdef : AST.ViewDef * err : ViewDefError
    /// The expression in the constraint generated an `ExprError`.
    | CEExpr of expr : AST.Expression * err : ExprError

/// Type of errors found when generating axioms.
type AxiomError = 
    /// The axiom uses a variable in global position incorrectly.
    | AEBadGlobal of var : Var.LValue * err : VarMapError
    /// The axiom uses a variable in local position incorrectly.
    | AEBadLocal of var : Var.LValue * err : VarMapError
    /// The axiom uses an expression incorrectly.
    | AEBadExpr of expr : AST.Expression * err : ExprError
    /// The axiom uses a view incorrectly.
    | AEBadView of view : AST.View * err : ViewError
    /// The axiom has a type mismatch in lvalue `bad`.
    | AETypeMismatch of expected : Var.Type * bad : Var.LValue * got : Var.Type
    /// The axiom uses a semantically invalid atomic action.
    | AEUnsupportedAtomic of atom : AST.AtomicAction * reason : string
    /// The axiom uses a semantically invalid command.
    | AEUnsupportedCommand of cmd : AST.Command<AST.View> * reason : string

/// Represents an error when converting a model.
type ModelError = 
    /// A view prototype in the program generated a `ViewProtoError`.
    | MEVProto of proto : AST.ViewProto * err : ViewProtoError
    /// A constraint in the program generated a `ConstraintError`.
    | MEConstraint of constr : AST.ViewDef * err : ConstraintError
    /// An axiom in the program generated an `AxiomError`.
    | MEAxiom of methname : string * err : AxiomError
    /// A variable in the program generated a `VarMapError`.
    | MEVar of err : VarMapError
