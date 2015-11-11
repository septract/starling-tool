namespace Starling

open Starling.AST

/// The stage of the Starling pipeline that assembles an AST into a
/// series of ordered definitions.
module Collator =
    /// A script whose items have been partitioned by type.
    type CollatedScript = {
        CGlobals:     ( Type * string ) list
        CLocals:     ( Type * string ) list
        CConstraints: Constraint list
        CMethods:     Method list
    }

    /// The empty collated script.
    let empty = { CConstraints = []; CMethods = []; CGlobals = []; CLocals = [] }

    /// Files a script item into the appropriate bin in a
    /// CollatedScript.
    let collateStep item collation =
        match item with
            | SGlobal     ( v, t ) -> { collation with CGlobals     = ( v, t ) :: collation.CGlobals }
            | SLocal      ( v, t ) -> { collation with CLocals      = ( v, t ) :: collation.CLocals }
            | SMethod     m        -> { collation with CMethods     = m :: collation.CMethods }
            | SConstraint c        -> { collation with CConstraints = c :: collation.CConstraints }

    /// Collates a script, grouping all like-typed ScriptItems together.
    let collate script =
        // We foldBack instead of fold to preserve the original order.
        List.foldBack collateStep script empty
