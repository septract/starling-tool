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
      [<Option('p', HelpText = "Stop at parsing and output what Starling parsed.")>]
      parse : bool
      [<Option('c', HelpText = "Stop at collating and output the collated script.")>]
      collate : bool
      [<Option('m', HelpText = "Stop at modelling and output the model.")>]
      model : bool
      [<Option('f', HelpText = "Stop at modelling and output the flattened model.")>]
      flatten : bool
      [<Option('e', HelpText = "Stop at expanding and output the expanded model.")>]
      expand : bool
      [<Option('s', HelpText = "Stop at semantic translation and output the translated model.")>]
      semantics : bool
      [<Option('F', HelpText = "Stop at framing and output the framed axioms.")>]
      frame : bool
      [<Option('T', HelpText = "Stop at term generation and output the unreified terms.")>]
      termgen : bool
      [<Option('r', HelpText = "Stop at term reification and output the reified terms.")>]
      reify : bool
      [<Option('R', HelpText = "Stop at term Z3 reification and output the reified terms.")>]
      reifyZ3 : bool
      [<Option('z', HelpText = "Output the Z3 queries instead of checking them.")>]
      z3 : bool
      [<Value(0, MetaName = "input", HelpText = "The file to load (omit, or supply -, for standard input).")>]
      input : string option }

type StarlingError = 
    | SEFrontend of Lang.Frontend.Error
    | SEOther of string

let printStarlingError = 
    function 
    | SEFrontend e -> Lang.Frontend.printError e
    | SEOther e -> Starling.Pretty.Types.String e

let printWarns header ws = 
    Starling.Pretty.Types.Header(header, 
                                 ws
                                 |> List.map Starling.Pretty.Types.Indent
                                 |> Starling.Pretty.Types.vsep)

let printResult pOk pBad = 
    either (pairMap pOk pBad >> function 
            | (ok, []) -> ok
            | (ok, ws) -> 
                Starling.Pretty.Types.vsep [ ok
                                             Starling.Pretty.Types.VSkip
                                             Starling.Pretty.Types.Separator
                                             Starling.Pretty.Types.VSkip
                                             printWarns "Warnings" ws ]) (pBad >> printWarns "Errors")

type OutputType = 
    | OutputTFrontend of Lang.Frontend.Request
    | OutputTFlatten
    | OutputTExpand
    | OutputTSemantics
    | OutputTFrame
    | OutputTTermGen
    | OutputTReify
    | OutputTReifyZ3
    | OutputTZ3
    | OutputTSat

[<NoComparison>]
type Output = 
    | OutputFrontend of Lang.Frontend.Response
    | OutputFlatten of Starling.Model.FlatModel
    | OutputExpand of Starling.Model.FullModel
    | OutputSemantics of Starling.Model.SemModel
    | OutputFrame of Starling.Model.FramedAxiom list
    | OutputTermGen of Starling.Model.Term list
    | OutputReify of Starling.Model.ReTerm list
    | OutputReifyZ3 of Starling.Model.ZTerm list
    | OutputZ3 of Z3.BoolExpr list
    | OutputSat of Z3.Status list

let printOutput = 
    function 
    | OutputFrontend f -> Lang.Frontend.printResponse f
    | OutputFlatten f -> Starling.Pretty.Misc.printFlatModel f
    | OutputExpand e -> Starling.Pretty.Misc.printFullModel e
    | OutputSemantics e -> Starling.Pretty.Misc.printSemModel e
    | OutputFrame f -> Starling.Pretty.Misc.printFramedAxioms f
    | OutputTermGen t -> Starling.Pretty.Misc.printTerms t
    | OutputReify t -> Starling.Pretty.Misc.printReTerms t
    | OutputReifyZ3 t -> Starling.Pretty.Misc.printZTerms t
    | OutputZ3 z -> Starling.Pretty.Misc.printZ3Exps z
    | OutputSat s -> Starling.Pretty.Misc.printSats s

let runStarlingZ3 semanticsR reifyR otype = 
    let z3R = lift2 Starling.Z3.Reifier.combineTerms semanticsR reifyR
    match otype with
    | OutputTZ3 -> lift OutputZ3 z3R
    | OutputTSat -> 
        lift2 (fun m zs -> 
            zs
            |> List.map (fun z -> 
                   let ctx = m.Context
                   let solver = ctx.MkSimpleSolver()
                   solver.Assert [| z |]
                   solver.Check [||])
            |> OutputSat) semanticsR z3R
    | _ -> fail (SEOther "this should be unreachable!")

let runStarlingReifyZ3 semanticsR reifyR otype = 
    let reifyZ3R = lift2 Starling.Z3.Reifier.reifyZ3 semanticsR reifyR
    match otype with
    | OutputTReifyZ3 -> lift OutputReifyZ3 reifyZ3R
    | _ -> runStarlingZ3 semanticsR reifyZ3R otype

let runStarlingReify semanticsR termGenR otype = 
    let reifyR = lift2 Starling.Reifier.reify semanticsR termGenR
    match otype with
    | OutputTReify -> lift OutputReify reifyR
    | _ -> runStarlingReifyZ3 semanticsR reifyR otype

let runStarlingTermGen semanticsR frameR otype = 
    let termGenR = lift2 Starling.TermGen.termGen semanticsR frameR
    match otype with
    | OutputTTermGen -> lift OutputTermGen termGenR
    | _ -> runStarlingReify semanticsR termGenR otype

let runStarlingFrame semanticsR otype = 
    let frameR = lift Starling.Framer.frame semanticsR
    match otype with
    | OutputTFrame -> lift OutputFrame frameR
    | _ -> runStarlingTermGen semanticsR frameR otype

let runStarlingSemantics modelR otype = 
    let semanticsR = lift Starling.Semantics.translate modelR
    match otype with
    | OutputTSemantics -> lift OutputSemantics semanticsR
    | _ -> runStarlingFrame semanticsR otype

let runStarlingExpand modelR otype = 
    let expandR = lift Starling.Expander.expand modelR
    match otype with
    | OutputTExpand -> lift OutputExpand expandR
    | _ -> runStarlingSemantics expandR otype

let runStarlingFlatten modelR otype = 
    let flattenR = lift Starling.Flattener.flatten modelR
    match otype with
    | OutputTFlatten -> lift OutputFlatten flattenR
    | _ -> runStarlingExpand flattenR otype

let runStarling file otype = 
    let frq = 
        match otype with
        | OutputTFrontend f -> f
        | _ -> Lang.Frontend.Request.Model
    Lang.Frontend.run frq file
    |> mapMessages StarlingError.SEFrontend
    |> match otype with
       | OutputTFrontend _ -> lift OutputFrontend
       | x -> 
           bind (function 
               | Lang.Frontend.Response.Model m -> runStarlingFlatten (ok m) x
               | v -> SEOther "internal error: bad frontend response" |> fail)

let otypeFromOpts opts = 
    [ (opts.parse, OutputTFrontend Lang.Frontend.Request.Parse)
      (opts.collate, OutputTFrontend Lang.Frontend.Request.Collate)
      (opts.model, OutputTFrontend Lang.Frontend.Request.Model)
      (opts.flatten, OutputTFlatten)
      (opts.expand, OutputTExpand)
      (opts.semantics, OutputTSemantics)
      (opts.frame, OutputTFrame)
      (opts.termgen, OutputTTermGen)
      (opts.reify, OutputTReify)
      (opts.reifyZ3, OutputTReifyZ3)
      (opts.z3, OutputTZ3) ]
    |> List.tryFind fst
    |> function 
    | Some(_, o) -> o
    | None -> OutputTSat

let starlingMain opts = 
    let input = opts.input
    let human = opts.human
    let otype = otypeFromOpts opts
    let starlingR = runStarling input otype
    
    let pfn = 
        if human then printOutput
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
