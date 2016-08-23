/// <summary>
///     The stage of the Starling language frontend that assembles an AST into
///     a set of collections of like-typed items.
/// </summary>
module Starling.Lang.Collator

open Starling.Utils
open Starling.Core.Var
open Starling.Core.View

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
        { Globals : TypedVar list
          Locals : TypedVar list
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
          Constraints : (DView * Expression option) list
          Methods : CMethod<Marked<View>> list }


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
    let printCollatedScript (cs: CollatedScript) : Doc =
        let definites =
            [ vsep <| Seq.map printViewProto cs.VProtos
              vsep <| Seq.map (printScriptVar "shared") cs.Globals
              vsep <| Seq.map (printScriptVar "local") cs.Locals
              vsep <| Seq.map (uncurry printConstraint) cs.Constraints
              VSep(List.map (printMethod
                                 (printMarkedView printView)
                                 (printCommand (printMarkedView printView)))
                            cs.Methods,
                   VSkip)]

        // Add in search, but only if it actually exists.
        let all =
            match cs.Search with
            | None -> definites
            | Some s -> printSearch s :: definites

        VSep(all, (vsep [ VSkip; Separator; Nop ]))


/// <summary>
///     The empty collated script.
/// </summary>
let empty : CollatedScript =
    { Constraints = []
      Methods = []
      Search = None
      VProtos = []
      Globals = []
      Locals = [] }

/// <summary>
///     Collates a script, grouping all like-typed items together.
/// </summary>
/// <param name="script">
///     The list of <c>ScriptItem</c>s to collate.
/// </param>
/// <returns>
///     The <c>CollatedScript</c> resulting from collating the
///     <c>ScriptItems</c> in <paramref name="script"/>.
/// </returns>
let collate (script : ScriptItem list) : CollatedScript =
    // TODO(CaptainHayashi): rewrite this into a recursion for perf?

    let collateStep item (cs : CollatedScript) =
        match item.Node with
        | Global g -> { cs with Globals = g::cs.Globals }
        | Local l -> { cs with Locals = l :: cs.Locals }
        | ViewProto v -> { cs with VProtos = v::cs.VProtos }
        | Search i -> { cs with Search = Some i }
        | Method m -> { cs with Methods = m::cs.Methods }
        | Constraint (v, d) -> { cs with Constraints = (v, d)::cs.Constraints }

    // We foldBack instead of fold to preserve the original order.
    List.foldBack collateStep script empty
