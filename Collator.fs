/// <summary>
///     The stage of the Starling language frontend that assembles an AST into
///     a set of collections of like-typed items.
/// </summary>
module Starling.Lang.Collator

open Starling.Utils
open Starling.Var

open Starling.Lang.AST


/// <summary>
///     Types for the collator stage.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A script whose items have been partitioned by type.
    /// </summary>
    type CollatedScript = 
        { Globals : (Type * string) list
          Locals : (Type * string) list
          VProtos : ViewProto list
          Constraints : Constraint list
          Methods : Method<View, Command<View>> list }


/// <summary>
///     Pretty printers for the collator stage.
/// </summary>
module Pretty =
    open Starling.Pretty.Types
    
    open Starling.Lang.AST.Pretty
    
    /// <summary>
    ///     Pretty-prints a collated script.
    /// </summary>
    /// <param name="cs">
    ///     The collated script to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command for printing <paramref name="cs" />.
    /// </returns>
    let printCollatedScript (cs: CollatedScript) = 
        VSep([ vsep <| List.map printViewProto cs.VProtos
               vsep <| List.map (uncurry (printScriptVar "shared")) cs.Globals
               vsep <| List.map (uncurry (printScriptVar "local")) cs.Locals
               vsep <| List.map printConstraint cs.Constraints
               VSep(List.map (printMethod printViewLine printCommand) cs.Methods, VSkip) ], (vsep [ VSkip; Separator; Nop ]))


/// <summary>
///     The empty collated script.
/// </summary>
let empty = 
    { Constraints = []
      Methods = []
      VProtos = []
      Globals = []
      Locals = [] }

/// <summary>
///     Files a script item into the appropriate bin in a collated script.
/// </summary>
/// <param name="item" />
///     The <c>ScriptItem</c> to place into <paramref name="cs" />.
/// </param>
/// <param name="cs" />
///     The <c>CollatedScript</c> to expand with <paramref name="item" />.
/// </param>
/// <returns>
///     The <c>CollatedScript</c> resulting from adding
///     <paramref name="item" /> to <paramref name="cs" />.
/// </returns>
let collateStep item cs = 
    match item with
    | Global(v, t) -> { cs with Globals = (v, t) :: cs.Globals }
    | Local(v, t) -> { cs with Locals = (v, t) :: cs.Locals }
    | ViewProto v -> { cs with VProtos = v :: cs.VProtos }
    | Method m -> { cs with Methods = m :: cs.Methods }
    | Constraint c -> { cs with Constraints = c :: cs.Constraints }

/// <summary>
///     Collates a script, grouping all like-typed items together.
/// </summary>
/// <param name="script" />
///     The <c>Script</c> to collate.
/// </param>
/// <returns>
///     The <c>CollatedScript</c> resulting from collating the
///     <c>ScriptItems</c> in <paramref name="script" />.
/// </returns>
let collate script = 
    // We foldBack instead of fold to preserve the original order.
    List.foldBack collateStep script empty
