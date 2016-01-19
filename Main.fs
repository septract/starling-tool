/// Main module for the Starling executable.
module Main

open Starling
open Starling.Model
open CommandLine
open Chessie.ErrorHandling

/// Command-line flags used in the Starling executable.
type Options = 
    { [<Option('h', HelpText = "If stopped at an intermediate stage, print the result for human consumption.")>]
      human : bool
      [<Option('s', HelpText = "The stage at which Starling should stop and output.")>]
      stage : string option
      [<Value(0, MetaName = "input", HelpText = "The file to load (omit, or supply -, for standard input).")>]
      input : string option }

/// Enumeration of possible requests to Starling.
type Request = 
    /// Run the language frontend only, with the given request.
    | Frontend of Lang.Frontend.Request
    /// Stop at structure flattening.
    | Flatten
    /// Stop at conditional expansion.
    | Expand
    /// Stop at semantic transformation.
    | Semantics
    /// Stop at frame-axiom-pair generation.
    | Frame
    /// Stop at term generation.
    | TermGen
    /// Stop at view reification.
    | Reify
    /// Run the Z3 backend, with the given request.
    | Z3 of Z3.Backend.Request
    /// Run the HSF backend (experimental).
    | HSF

/// Map of -s stage names to Request items.
let requestMap = 
    Map.ofList [ ("parse", Request.Frontend Lang.Frontend.Request.Parse)
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
                 ("sat", Request.Z3 Z3.Backend.Request.Sat)
                 ("hsf", Request.HSF) ]

/// Converts an optional -s stage name to a request item.
/// If none is given, the latest stage is selected.
let requestFromStage ostage = Map.tryFind (withDefault "sat" ostage) requestMap

/// Type of possible outputs from a Starling run.
[<NoComparison>]
type Response = 
    /// The result of frontend processing.
    | Frontend of Lang.Frontend.Response
    /// The result of structure flattening.
    | Flatten of Model<FlatAxiom>
    /// The result of conditional expansion.
    | Expand of Model<FullAxiom>
    /// The result of semantic expansion.
    | Semantics of Model<SemAxiom>
    /// The result of frame-axiom-pair generation.
    | Frame of Model<FramedAxiom>
    /// The result of term generation.
    | TermGen of Model<Term>
    /// The result of view reification.
    | Reify of Model<ReTerm>
    /// The result of Z3 backend processing.
    | Z3 of Z3.Backend.Response
    /// The result of HSF processing.
    | HSF of Horn.Horn list

/// Pretty-prints a response.
let printResponse = 
    function 
    | Frontend f -> Lang.Frontend.printResponse f
    | Flatten f -> Starling.Pretty.Misc.printFlatModel f
    | Expand e -> Starling.Pretty.Misc.printFullModel e
    | Semantics e -> Starling.Pretty.Misc.printSemModel e
    | Frame {Axioms = f} -> Starling.Pretty.Misc.printFramedAxioms f
    | TermGen {Axioms = t} -> Starling.Pretty.Misc.printTerms t
    | Reify {Axioms = t} -> Starling.Pretty.Misc.printReTerms t
    | Z3 z -> Z3.Backend.printResponse z
    | HSF h -> Starling.Pretty.Horn.printHorns h

/// A top-level program error.
type Error = 
    /// An error occurred in the frontend.
    | Frontend of Lang.Frontend.Error
    /// An error occurred in the Z3 backend.
    | Z3 of Z3.Backend.Error
    /// An error occurred in the HSF backend.
    | HSF of Errors.Horn.Error
    /// A stage was requested using the -s flag that does not exist.
    | BadStage
    /// A miscellaneous (internal) error has occurred.
    | Other of string

/// Prints a top-level program error.
let printError = 
    function 
    | Frontend e -> Lang.Frontend.printError e
    | Z3 e -> Z3.Backend.printError e
    | HSF e -> Starling.Pretty.Errors.printHornError e
    | BadStage -> 
        Pretty.Types.colonSep [ Pretty.Types.String "Bad stage"
                                Pretty.Types.String "try"
                                requestMap
                                |> Map.toSeq
                                |> Seq.map (fst >> Pretty.Types.String)
                                |> Pretty.Types.commaSep ]
    | Other e -> Pretty.Types.String e

/// Pretty-prints a list of error or warning strings, with the given
/// header.
let printWarns header ws = 
    Starling.Pretty.Types.Header(header, 
                                 ws
                                 |> List.map Pretty.Types.Indent
                                 |> Pretty.Types.vsep)

/// Pretty-prints a Chessie result, given printers for the successful
/// case and failure messages.
let printResult pOk pBad = 
    either (pairMap pOk pBad >> function 
            | (ok, []) -> ok
            | (ok, ws) -> 
                Starling.Pretty.Types.vsep [ ok
                                             Starling.Pretty.Types.VSkip
                                             Starling.Pretty.Types.Separator
                                             Starling.Pretty.Types.VSkip
                                             printWarns "Warnings" ws ]) (pBad >> printWarns "Errors")

let hsf = bind (Starling.HSF.hsfModel >> mapMessages Error.HSF)

/// Shorthand for the Z3 stage.
let z3 rq = bind (Starling.Z3.Backend.run rq >> mapMessages Error.Z3)

/// Shorthand for the reify stage.
let reify = lift Starling.Reifier.reify

/// Shorthand for the term generation stage.
let termGen = lift Starling.TermGen.termGen

/// Shorthand for the framing stage.
let frame = lift Starling.Framer.frame

/// Shorthand for the semantics stage.
let semantics = lift Starling.Semantics.translate

/// Shorthand for the expand stage.
let expand = lift Starling.Expander.expand

/// Shorthand for the flatten stage.
let flatten = lift Starling.Flattener.flatten

/// Shorthand for the frontend stage.
let frontend rq = Lang.Frontend.run rq >> mapMessages Error.Frontend

/// Shorthand for the full frontend stage.
let model = 
    frontend Lang.Frontend.Request.Model >> bind (function 
                                                | Lang.Frontend.Response.Model m -> m |> ok
                                                | _ -> Other "internal error: bad frontend response" |> fail)

/// Given two arguments rq and file, runs the Starling request rq on the file named by file.
/// file is optional: if missing, we read from stdin.
let runStarling = 
    function 
    | Request.Frontend rq -> frontend rq >> lift Response.Frontend
    | Request.Flatten -> 
        model
        >> flatten
        >> lift Response.Flatten
    | Request.Expand -> 
        model
        >> flatten
        >> expand
        >> lift Response.Expand
    | Request.Semantics -> 
        model
        >> flatten
        >> expand
        >> semantics
        >> lift Response.Semantics
    | Request.Frame -> 
        model
        >> flatten
        >> expand
        >> semantics
        >> frame
        >> lift Response.Frame
    | Request.TermGen -> 
        model
        >> flatten
        >> expand
        >> semantics
        >> frame
        >> termGen
        >> lift Response.TermGen
    | Request.Reify -> 
        model
        >> flatten
        >> expand
        >> semantics
        >> frame
        >> termGen
        >> reify
        >> lift Response.Reify
    | Request.Z3 rq -> 
        model
        >> flatten
        >> expand
        >> semantics
        >> frame
        >> termGen
        >> reify
        >> z3 rq
        >> lift Response.Z3
    | Request.HSF ->
        model
        >> flatten
        >> expand
        >> semantics
        >> frame
        >> termGen
        >> reify
        >> hsf
        >> lift Response.HSF

/// Runs Starling with the given options, and outputs the results.
let mainWithOptions opts = 
    let input = opts.input
    let human = opts.human
    
    let starlingR = 
        match (requestFromStage opts.stage) with
        | Some otype -> runStarling otype input
        | None -> fail Error.BadStage
    
    let pfn = 
        if human then printResponse
        else (sprintf "%A" >> Starling.Pretty.Types.String)
    
    printResult pfn (List.map printError) starlingR
    |> Starling.Pretty.Types.print
    |> printfn "%s"
    0

[<EntryPoint>]
let main argv = 
    match CommandLine.Parser.Default.ParseArguments<Options> argv with
    | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value
    | :? NotParsed<Options> as notParsed -> 
        printfn "failure: %A" notParsed.Errors
        2
    | _ -> 
        printfn "parse result of unknown type"
        3
