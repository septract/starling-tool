/// Errors encountered when working with variables.
module Starling.Errors.Var

/// Represents an error when building or converting a variable map.
type VarMapError = 
    | Duplicate of name : string
    // The variable was not found.
    | NotFound of name : string
