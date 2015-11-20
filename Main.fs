open Starling
open Starling.Model

open System
open CommandLine
open CommandLine.Text

open Fuchu
open FParsec // TODO: push fparsec references out of Main.
open Microsoft.Z3 // TODO: this too.

// This is down here to force Chessie's fail to override FParsec's.
open Chessie.ErrorHandling

type Options = {
    [<Option('t',
             HelpText = "Ignore input and run regression tests.")>]
    test: bool;
    [<Option('h',
             HelpText = "If stopped at an intermediate stage, print the result for human consumption.")>]
    human: bool;

    // The following are supposed to be mutually exclusive, but as the
    // V2 API of CommandLine is somewhat unclear, they are currently
    // inclusive and the exclusivity is bodged earlier.
    [<Option('p',
             HelpText = "Stop at parsing and output what Starling parsed.")>]
    parse: bool;
    [<Option('c',
             HelpText = "Stop at collating and output the collated script.")>]
    collate: bool;
    [<Option('m',
             HelpText = "Stop at modelling and output the model..")>]
    model: bool;

    [<Value(0,
            MetaName = "input",
            HelpText = "The file to load (omit, or supply -, for standard input).")>]
    input: string option;
}

/// Errors occurring during the operation of Starling.
type StarlingError =
    | SEParse of string
    | SEModel of Starling.Errors.Modeller.ModelError
    | SEOther of string

/// Pretty-prints a Starling error.
let printStarlingError err =
    match err with
        | SEParse e -> e
        | SEModel e -> Starling.Pretty.printModelError e
        | SEOther e -> e

/// Pretty-prints a list of error or warning strings, with the given
/// header.
let printWarns header ws =
    header + ":\n  " + String.concat "\n  " ws

/// Pretty-prints a Chessie result, given printers for the successful
/// case and failure messages.
let printResult pOk pBad =
    either ( pairMap pOk pBad >> (
                fun okbad ->
                    // Only show warnings if there actually were some.
                    match okbad with
                        | ( ok, [] ) -> ok
                        | ( ok, ws ) -> ok + "\n\n" + printWarns "Warnings" ws
            )
           )
           ( pBad >> (
                fun bad -> printWarns "Errors" bad
            )
           )

let parseFile name =
    // If - or no name was given, parse from the console.
    let stream, streamName =
        match name with
            | Some("-") -> (Console.OpenStandardInput ()      , "(stdin)")
            | None      -> (Console.OpenStandardInput ()      , "(stdin)")
            | Some(nam) -> (IO.File.OpenRead(nam) :> IO.Stream, nam      )

    let pres = runParserOnStream Starling.Parser.parseScript () streamName stream Text.Encoding.UTF8
    match pres with
        | Success ( result,   _, _ ) -> ok result
        | Failure ( errorMsg, _, _ ) -> fail errorMsg

(*
    Starling can output the results of various stages in its pipeline;
    the OutputType and Output types provide framework for the user to
    decide in which stage it halts.
*)

/// Set of possible outputs Starling can provide.
type OutputType =
    | OutputTParse
    | OutputTCollation
    | OutputTModel

/// The output from a Starling run.
type Output =
    | OutputParse     of Starling.AST.ScriptItem list
    | OutputCollation of Starling.Collator.CollatedScript
    | OutputModel     of Starling.Model.Model

let printOutput out =
    match out with
        | OutputParse     s -> Starling.Pretty.printScript s
        | OutputCollation c -> Starling.Pretty.printCollatedScript c
        | OutputModel     m -> Starling.Pretty.printModel m

(*
    Starling pipeline (here defined in reverse):

    1) Parse AST;
    2) Collate AST into buckets of variable, constraint, method defs;
    3) Make model from AST;
    4) Run proof on model.

    The Starling pipeline can be halted at the end of any of these
    stages, producing the various Output types above (in addition to
    just dumping the AST directly).
*)

/// Runs the model generator and further Starling processes.
let runStarlingModel ctx collatedR otype =
    // Convert the errors from ModelError to StarlingError.
    let modelR = bind ( Starling.Modeller.model ctx >> mapMessages SEModel ) collatedR

    match otype with
        | OutputTModel -> lift OutputModel modelR
        | _            -> fail ( SEOther "this should be unreachable!" )

/// Runs the collation and further Starling processes on Starling.
let runStarlingCollate ctx scriptR otype =
    // Collation cannot fail, so lift instead of bind.
    let collatedR = lift Starling.Collator.collate scriptR

    match otype with
        | OutputTCollation -> lift OutputCollation collatedR
        | _                -> runStarlingModel ctx collatedR otype

/// Runs Starling on the given file script.
let runStarling ctx file otype =
    let scriptPR = parseFile file
    // Convert the errors from string to StarlingError.
    let scriptR  = mapMessages SEParse scriptPR

    match otype with
        | OutputTParse -> lift OutputParse scriptR
        | _            -> runStarlingCollate ctx scriptR otype

/// Deduces the output type from the options.
let otypeFromOpts opts =
    // We stop at the earliest chosen stopping point,
    // and default to the latest if no option has been given.
    match ( opts.parse, opts.collate, opts.model ) with
        | ( true , _    , _ ) -> OutputTParse
        | ( false, true , _ ) -> OutputTCollation
        | ( false, false, _ ) -> OutputTModel

/// Runs Starling and outputs the results.
let starlingMain opts =
    let input = opts.input
    let human = opts.human
    let otype = otypeFromOpts opts

    let ctx       = new Context ()
    let starlingR = runStarling ctx input otype
    ctx.Dispose ()

    let pfn = if human then printOutput else fun a -> sprintf "%A" a

    printfn "%s" <| printResult pfn
                                ( List.map printStarlingError )
                                starlingR
    0


let mainWithOptions opts argv =
    if opts.test
    then defaultMainThisAssembly argv
    else starlingMain opts

[<EntryPoint>]
let main argv =
    let result = CommandLine.Parser.Default.ParseArguments<Options>(argv)
    match result with
        | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value argv
        | :? NotParsed<Options> as notParsed -> printfn "failure: %A" notParsed.Errors
                                                2
        | _ -> printfn "parse result of unknown type"
               3
