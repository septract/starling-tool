/// <summary>
///     The stage of the Starling language frontend that assembles an AST into
///     a set of collections of like-typed items.
/// </summary>
module Starling.Lang.Collator

open Starling.Utils
open Starling.Core.Var

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
          /// <summary>
          ///     The search depth, defaulting to <c>None</c> (no search).
          /// </summary>
          /// <remarks>
          ///     <para>
          ///          No search is different from a search of depth 0:
          ///          the latter includes the empty view.
          ///     </para>
          /// </remarks>
          Search : int option
          VProtos : ViewProto list
          Constraints : Constraint list
          Methods : Method<View, Command<View>> list }


/// <summary>
///     Pretty printers for the collator stage.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

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
        let definites =
            [ vsep <| Seq.map printViewProto cs.VProtos
              vsep <| Seq.map (uncurry (printScriptVar "shared")) cs.Globals
              vsep <| Seq.map (uncurry (printScriptVar "local")) cs.Locals
              vsep <| Seq.map printConstraint cs.Constraints
              VSep(List.map (printMethod printView printCommand) cs.Methods, VSkip)]

        // Add in search, but only if it actually exists.
        let all =
            match cs.Search with
            | None -> definites
            | Some s -> printSearch s :: definites

        VSep(all, (vsep [ VSkip; Separator; Nop ]))


/// <summary>
///     The empty collated script.
/// </summary>
let empty =
    { Constraints = []
      Methods = []
      Search = None
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
    | Search i -> { cs with Search = Some i }
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
