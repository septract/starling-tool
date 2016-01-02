// This is down here to force Chessie's fail to override FParsec's.
// The following are supposed to be mutually exclusive, but as the
// V2 API of CommandLine is somewhat unclear, they are currently
// inclusive and the exclusivity is bodged earlier.
/// Errors occurring during the operation of Starling.
/// Pretty-prints a Starling error.
/// Pretty-prints a list of error or warning strings, with the given
/// header.
/// Pretty-prints a Chessie result, given printers for the successful
/// case and failure messages.
// Only show warnings if there actually were some.
(* Starling can output the results of various stages in its pipeline;
 * the OutputType and Output types provide framework for the user to
 * decide in which stage it halts.
 *)

/// Set of possible outputs Starling can provide.
/// The output from a Starling run.
// TODO(CaptainHayashi): commandify AST printing.
(*
    Starling pipeline (here defined in reverse):

    1) Parse AST;
    2) Collate AST into buckets of variable, constraint, method defs;
    3) Make model from AST, with ‘partially resolved’ (structured) axioms;
    4) Flatten model to produce flattened axioms;
    5) Expand conditionals in axioms into guarded axioms;
    6) Expand primitives in axioms into Z3 relations;
    7) Run proof on model.

    The Starling pipeline can be halted at the end of any of these
    stages, producing the various Output types above (in addition to
    just dumping the AST directly).
*)

/// Runs Starling, either outputting or checking the Z3 term.
/// Runs the Z3 reifier and further Starling processes.
/// Runs the reifier and further Starling processes.
/// Runs the term generator and further Starling processes.
/// Runs the framed axiom generator and further Starling processes.
/// Runs the model expander and further Starling processes.
/// Runs the model expander and further Starling processes.
/// Runs the model flattener and further Starling processes.
/// Runs the model generator and further Starling processes.
// Convert the errors from ModelError to StarlingError.
// This stage has the responsibility for disposing of the Z3 context.
/// Runs the collation and further Starling processes.
// Collation cannot fail, so lift instead of bind.
/// Runs Starling on the given file script.
// Convert the errors from string to StarlingError.
/// Deduces the output type from the options.
// We stop at the earliest chosen stopping point,
// and default to the latest if no option has been given.
/// Runs Starling and outputs the results.
module Main

open Starling
open Starling.Model
open CommandLine
open CommandLine.Text
open Microsoft
open Fuchu
open Chessie.ErrorHandling

type Options = 
    { [<Option('t', HelpText = "Ignore input and run regression tests.")>]
      test : bool
      [<Option('h', HelpText = "If stopped at an intermediate stage, print the result for human consumption.")>]
      human : bool
      [<Option('s', HelpText = "The stage at which Starling should stop and output.")>]
      stage : string option
      [<Value(0, MetaName = "input", HelpText = "The file to load (omit, or supply -, for standard input).")>]
      input : string option }

type Request = 
    | Frontend of Lang.Frontend.Request
    | Flatten
    | Expand
    | Semantics
    | Frame
    | TermGen
    | Reify
    | Z3 of Z3.Backend.Request

[<NoComparison>]
type Response = 
    | Frontend of Lang.Frontend.Response
    | Flatten of Starling.Model.FlatModel
    | Expand of Starling.Model.FullModel
    | Semantics of Starling.Model.SemModel
    | Frame of Starling.Model.FramedAxiom list
    | TermGen of Starling.Model.Term list
    | Reify of Starling.Model.ReTerm list
    | Z3 of Z3.Backend.Response

let printResponse = 
    function 
    | Frontend f -> Lang.Frontend.printResponse f
    | Flatten f -> Starling.Pretty.Misc.printFlatModel f
    | Expand e -> Starling.Pretty.Misc.printFullModel e
    | Semantics e -> Starling.Pretty.Misc.printSemModel e
    | Frame f -> Starling.Pretty.Misc.printFramedAxioms f
    | TermGen t -> Starling.Pretty.Misc.printTerms t
    | Reify t -> Starling.Pretty.Misc.printReTerms t
    | Z3 z -> Z3.Backend.printResponse z

let requestMap =
    Map.ofList
        [ ("parse", Request.Frontend Lang.Frontend.Request.Parse)
          ("collate", Request.Frontend Lang.Frontend.Request.Collate)
          ("model", Request.Frontend Lang.Frontend.Request.Model)
          ("flatten", Request.Flatten)
          ("expand", Request.Expand)
          ("semantics", Request.Semantics)
          ("frame", Request.Frame)
          ("termgen", Request.TermGen)
          ("reify", Request.Reify)
          ("reifyZ3", Request.Z3 Z3.Backend.Request.Translate)
          ("z3", Request.Z3 Z3.Backend.Request.Combine)
          ("sat", Request.Z3 Z3.Backend.Request.Sat) ]

type StarlingError = 
    | Frontend of Lang.Frontend.Error
    | BadStage
    | Other of string

let printStarlingError = 
    function 
    | Frontend e -> Lang.Frontend.printError e
    | BadStage -> Pretty.Types.colonSep [ Pretty.Types.String "Bad stage"
                                          Pretty.Types.String "try"
                                          requestMap
                                          |> Map.toSeq
                                          |> Seq.map (fst >> Pretty.Types.String)
                                          |> Pretty.Types.commaSep ]
    | Other e -> Pretty.Types.String e

let printWarns header ws = 
    Starling.Pretty.Types.Header(header, 
                                 ws
                                 |> List.map Pretty.Types.Indent
                                 |> Pretty.Types.vsep)

let printResult pOk pBad = 
    either (pairMap pOk pBad >> function 
            | (ok, []) -> ok
            | (ok, ws) -> 
                Starling.Pretty.Types.vsep [ ok
                                             Starling.Pretty.Types.VSkip
                                             Starling.Pretty.Types.Separator
                                             Starling.Pretty.Types.VSkip
                                             printWarns "Warnings" ws ]) (pBad >> printWarns "Errors")

let runStarlingZ3 semanticsR reifyR = 
    function 
    | Request.Z3 r -> lift2 (fun sr rr -> Starling.Z3.Backend.run sr r rr |> Response.Z3) semanticsR reifyR
    | _ -> fail (Other "this should be unreachable!")

let runStarlingReify semanticsR termGenR req = 
    let reifyR = lift2 Starling.Reifier.reify semanticsR termGenR
    match req with
    | Request.Reify -> lift Response.Reify reifyR
    | _ -> runStarlingZ3 semanticsR reifyR req

let runStarlingTermGen semanticsR frameR req = 
    let termGenR = lift2 Starling.TermGen.termGen semanticsR frameR
    match req with
    | Request.TermGen -> lift Response.TermGen termGenR
    | _ -> runStarlingReify semanticsR termGenR req

let runStarlingFrame semanticsR req = 
    let frameR = lift Starling.Framer.frame semanticsR
    match req with
    | Request.Frame -> lift Response.Frame frameR
    | _ -> runStarlingTermGen semanticsR frameR req

let runStarlingSemantics modelR req = 
    let semanticsR = lift Starling.Semantics.translate modelR
    match req with
    | Request.Semantics -> lift Response.Semantics semanticsR
    | _ -> runStarlingFrame semanticsR req

let runStarlingExpand modelR req = 
    let expandR = lift Starling.Expander.expand modelR
    match req with
    | Request.Expand -> lift Response.Expand expandR
    | _ -> runStarlingSemantics expandR req

let runStarlingFlatten modelR req = 
    let flattenR = lift Starling.Flattener.flatten modelR
    match req with
    | Request.Flatten -> lift Response.Flatten flattenR
    | _ -> runStarlingExpand flattenR req

let runStarling file req = 
    let frq = 
        match req with
        | Request.Frontend f -> f
        | _ -> Lang.Frontend.Request.Model
    Lang.Frontend.run frq file
    |> mapMessages StarlingError.Frontend
    |> match req with
       | Request.Frontend _ -> lift Response.Frontend
       | x -> 
           bind (function 
               | Lang.Frontend.Response.Model m -> runStarlingFlatten (ok m) x
               | v -> Other "internal error: bad frontend response" |> fail)

let requestFromStage ostage = 
    Map.tryFind (withDefault "sat" ostage) requestMap

let starlingMain opts = 
    let input = opts.input
    let human = opts.human
    let starlingR =
        match (requestFromStage opts.stage) with
        | Some otype -> runStarling input otype
        | None -> fail StarlingError.BadStage
    
    let pfn = 
        if human then printResponse
        else (sprintf "%A" >> Starling.Pretty.Types.String)
    printResult pfn (List.map printStarlingError) starlingR
    |> Starling.Pretty.Types.print
    |> printfn "%s"
    0

let mainWithOptions opts argv = 
    if opts.test then defaultMainThisAssembly argv
    else starlingMain opts

[<EntryPoint>]
let main argv = 
    match CommandLine.Parser.Default.ParseArguments<Options> argv with
    | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value argv
    | :? NotParsed<Options> as notParsed -> 
        printfn "failure: %A" notParsed.Errors
        2
    | _ -> 
        printfn "parse result of unknown type"
        3
