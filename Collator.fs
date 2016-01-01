/// The stage of the Starling pipeline that assembles an AST into a
/// series of ordered definitions.
module Starling.Lang.Collator

open Starling.Var
open Starling.Lang.AST

/// A script whose items have been partitioned by type.
type CollatedScript = 
    { Globals : (Type * string) list
      Locals : (Type * string) list
      VProtos : ViewProto list
      Constraints : Constraint list
      Methods : Method list }

/// The empty collated script.
let empty = 
    { Constraints = []
      Methods = []
      VProtos = []
      Globals = []
      Locals = [] }

/// Files a script item into the appropriate bin in a
/// CollatedScript.
let collateStep item collation = 
    match item with
    | Global(v, t) -> { collation with Globals = (v, t) :: collation.Globals }
    | Local(v, t) -> { collation with Locals = (v, t) :: collation.Locals }
    | ViewProto v -> { collation with VProtos = v :: collation.VProtos }
    | Method m -> { collation with Methods = m :: collation.Methods }
    | Constraint c -> { collation with Constraints = c :: collation.Constraints }

/// Collates a script, grouping all like-typed ScriptItems together.
let collate script = 
    // We foldBack instead of fold to preserve the original order.
    List.foldBack collateStep script empty
