namespace Starling

open Starling.AST

/// The stage of the Starling pipeline that assembles an AST into a
/// series of ordered definitions.
module Collator =
    /// A script whose items have been partitioned by type.
    type CollatedScript = {
        Globals:     ( Type * string ) list
        Locals:     ( Type * string ) list
        Constraints: Constraint list
        Methods:     Method list
    }

    /// The empty collated script.
    let empty = { Constraints = []; Methods = []; Globals = []; Locals = [] }

    /// Files a script item into the appropriate bin in a
    /// CollatedScript.
    let collateStep item collation =
        match item with
            | SGlobal     ( v, t ) -> { collation with Globals     = ( v, t ) :: collation.Globals }
            | SLocal      ( v, t ) -> { collation with Locals      = ( v, t ) :: collation.Locals }
            | SMethod     m        -> { collation with Methods     = m :: collation.Methods }
            | SConstraint c        -> { collation with Constraints = c :: collation.Constraints }

    /// Collates a script, grouping all like-typed ScriptItems together.
    let collate script =
        // We foldBack instead of fold to preserve the original order.
        List.foldBack collateStep script empty
