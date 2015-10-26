open Starling

open System
open CommandLine
open CommandLine.Text

open FParsec // TODO: push fparsec references out of Main.

type Options = {
    [<Value(0,
            MetaName = "input",
            HelpText = "The file to load (omit, or supply -, for standard input).")>]
    input: string option;
}

let parseFile name =
    let (stream, streamName) =
        match name with
            | Some("-") -> (Console.OpenStandardInput(),        "(stdin)")
            | None      -> (Console.OpenStandardInput(),        "(stdin)")
            | Some(nam) -> (IO.File.OpenRead(nam) :> IO.Stream, nam      )
    let pres = runParserOnStream Starling.Parser.parseScript () streamName stream Text.Encoding.UTF8
    match pres with
        | Success(result, _, _)   -> printfn "Success: %A" result
        | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg

[<EntryPoint>]
let main argv =
    let result = CommandLine.Parser.Default.ParseArguments<Options>(argv)
    match result with
        | :? Parsed<Options> as parsed -> parseFile parsed.Value.input
        | :? NotParsed<Options> as notParsed -> printfn "failure: %A" notParsed.Errors
    0
