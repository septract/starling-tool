open Starling
open Starling.Model

open System
open CommandLine
open CommandLine.Text

open Chessie.ErrorHandling
open Fuchu
open FParsec // TODO: push fparsec references out of Main.
open Microsoft.Z3 // TODO: this too.

type Options = {
    [<Option('t',
             HelpText = "Ignore input and run regression tests.")>]
    test: bool;
    [<Option('p',
             HelpText = "Pretty-prints the input instead of attempting to verify it.")>]
    pprint: bool;
    [<Value(0,
            MetaName = "input",
            HelpText = "The file to load (omit, or supply -, for standard input).")>]
    input: string option;
}

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

/// Runs Starling on the given parsed script.
let runStarlingOnScript script =
    // TODO(CaptainHayashi): eventually this will run the actual prover
    printfn "AST: \n%A" script
    printfn "---"

    let ctx         = new Context ()
    let collated    = Starling.Collator.collate script
    let modelResult = Starling.Z3.model ctx collated
    printfn "%s" <| printResult Starling.Pretty.printModel
                                ( List.map Starling.Pretty.printModelError )
                                modelResult

    printfn "---"

let parseFile name pprint =
    let (stream, streamName) =
        match name with
            | Some("-") -> (Console.OpenStandardInput(),        "(stdin)")
            | None      -> (Console.OpenStandardInput(),        "(stdin)")
            | Some(nam) -> (IO.File.OpenRead(nam) :> IO.Stream, nam      )
    let pres = runParserOnStream Starling.Parser.parseScript () streamName stream Text.Encoding.UTF8
    match pres with
        | Success(result, _, _)   -> if pprint
                                     then printfn "%s" ( Starling.Pretty.printScript result )
                                     else runStarlingOnScript result
        | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg

    0

let mainWithOptions opts argv =
    if opts.test
    then defaultMainThisAssembly argv
    else parseFile opts.input opts.pprint

[<EntryPoint>]
let main argv =
    let result = CommandLine.Parser.Default.ParseArguments<Options>(argv)
    match result with
        | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value argv
        | :? NotParsed<Options> as notParsed -> printfn "failure: %A" notParsed.Errors
                                                2
        | _ -> printfn "parse result of unknown type"
               3
