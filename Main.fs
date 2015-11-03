open Starling

open System
open CommandLine
open CommandLine.Text

open Fuchu
open FParsec // TODO: push fparsec references out of Main.

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
                                     else printfn "Success: %A" result
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
