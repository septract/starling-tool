/// Errors encountered when working with variables.
module Starling.Errors.Var

/// Represents an error when building or converting a variable map.
type VarMapError =
    | VMEDuplicate of name: string
      // The variable was not found.
    | VMENotFound of name: string
