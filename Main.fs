open Starling
open Starling.Model

open System
open CommandLine
open CommandLine.Text

open Microsoft
open Fuchu

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
             HelpText = "Stop at modelling and output the model.")>]
    model: bool;
    [<Option('f',
             HelpText = "Stop at modelling and output the flattened model.")>]
    flatten: bool;
    [<Option('e',
             HelpText = "Stop at expanding and output the expanded model.")>]
    expand: bool;
    [<Option('s',
             HelpText = "Stop at semantic translation and output the translated model.")>]
    semantics: bool;
    [<Option('F',
             HelpText = "Stop at framing and output the framed axioms.")>]
    frame: bool;
    [<Option('T',
             HelpText = "Stop at term generation and output the unreified terms.")>]
    termgen: bool;
    [<Option('r',
             HelpText = "Stop at term reification and output the reified terms.")>]
    reify: bool;
    [<Option('z',
             HelpText = "Output the Z3 queries instead of checking them.")>]
    z3: bool;
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
        | SEModel e -> Starling.Pretty.Misc.printModelError e
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
    | OutputTFlatten
    | OutputTExpand
    | OutputTSemantics
    | OutputTFrame
    | OutputTTermGen
    | OutputTReify
    | OutputTZ3
    | OutputTSat

/// The output from a Starling run.
type Output =
    | OutputParse of Starling.AST.ScriptItem list
    | OutputCollation of Starling.Collator.CollatedScript
    | OutputModel of Starling.Model.PartModel
    | OutputFlatten of Starling.Model.FlatModel
    | OutputExpand of Starling.Model.FullModel
    | OutputSemantics of Starling.Model.SemModel
    | OutputFrame of Starling.Model.FramedAxiom list
    | OutputTermGen of Starling.Model.Term list
    | OutputReify of Starling.Model.ReTerm list
    | OutputZ3 of Z3.BoolExpr list
    | OutputSat of Z3.Status list

let printOutput out =
    match out with
    | OutputParse s -> Starling.Pretty.AST.printScript s
    | OutputCollation c -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printCollatedScript c)
    | OutputModel m -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printPartModel m)
    | OutputFlatten f -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printFlatModel f)
    | OutputExpand e -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printFullModel e)
    | OutputSemantics e -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printSemModel e)
    | OutputFrame f -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printFramedAxioms f)
    | OutputTermGen t -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printTerms t)
    | OutputReify t -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printReTerms t)
    | OutputZ3 z -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printZ3Exps z)
    | OutputSat s -> Starling.Pretty.Types.print (Starling.Pretty.Misc.printSats s)

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
let runStarlingZ3 semanticsR reifyR otype =
    let z3R = lift2 Starling.Reifier.combineTerms semanticsR reifyR

    match otype with
    | OutputTZ3 -> lift OutputZ3 z3R
    | OutputTSat ->
        lift2
            (fun m zs ->
                zs
                |> List.map (fun z ->
                                let ctx = m.Context
                                let solver = ctx.MkSimpleSolver ()
                                solver.Assert [|z|]
                                solver.Check [||])
                |> OutputSat)
            semanticsR
            z3R
    | _ -> fail ( SEOther "this should be unreachable!" )

/// Runs the reifier and further Starling processes.
let runStarlingReify semanticsR termGenR otype =
    let reifyR = lift2 Starling.Reifier.reify semanticsR termGenR

    match otype with
    | OutputTReify -> lift OutputReify reifyR
    | _ -> runStarlingZ3 semanticsR reifyR otype

/// Runs the term generator and further Starling processes.
let runStarlingTermGen semanticsR frameR otype =
    let termGenR = lift2 Starling.TermGen.termGen semanticsR frameR

    match otype with
    | OutputTTermGen -> lift OutputTermGen termGenR
    | _ -> runStarlingReify semanticsR termGenR otype

/// Runs the framed axiom generator and further Starling processes.
let runStarlingFrame semanticsR otype =
    let frameR = lift Starling.Framer.frame semanticsR

    match otype with
    | OutputTFrame -> lift OutputFrame frameR
    | _ -> runStarlingTermGen semanticsR frameR otype

/// Runs the model expander and further Starling processes.
let runStarlingSemantics modelR otype =
    let semanticsR = lift Starling.Semantics.translate modelR

    match otype with
    | OutputTSemantics -> lift OutputSemantics semanticsR
    | _ -> runStarlingFrame semanticsR otype

/// Runs the model expander and further Starling processes.
let runStarlingExpand modelR otype =
    let expandR = lift Starling.Expander.expand modelR

    match otype with
    | OutputTExpand -> lift OutputExpand expandR
    | _ -> runStarlingSemantics expandR otype

/// Runs the model flattener and further Starling processes.
let runStarlingFlatten modelR otype =
    let flattenR = lift Starling.Flattener.flatten modelR

    match otype with
    | OutputTFlatten -> lift OutputFlatten flattenR
    | _ -> runStarlingExpand flattenR otype

/// Runs the model generator and further Starling processes.
let runStarlingModel collatedR otype =
    // Convert the errors from ModelError to StarlingError.
    let modelR = bind ( Starling.Modeller.model >> mapMessages SEModel ) collatedR

    let om =
        match otype with
        | OutputTModel -> lift OutputModel modelR
        | _            -> runStarlingFlatten modelR otype

    // This stage has the responsibility for disposing of the Z3 context.
    ignore (lift Starling.Model.disposeZ3 modelR)
    om

/// Runs the collation and further Starling processes.
let runStarlingCollate scriptR otype =
    // Collation cannot fail, so lift instead of bind.
    let collatedR = lift Starling.Collator.collate scriptR

    match otype with
    | OutputTCollation -> lift OutputCollation collatedR
    | _                -> runStarlingModel collatedR otype

/// Runs Starling on the given file script.
let runStarling file otype =
    let scriptPR = Starling.Parser.parseFile file
    // Convert the errors from string to StarlingError.
    let scriptR  = mapMessages SEParse scriptPR

    match otype with
        | OutputTParse -> lift OutputParse scriptR
        | _            -> runStarlingCollate scriptR otype

/// Deduces the output type from the options.
let otypeFromOpts opts =
    // We stop at the earliest chosen stopping point,
    // and default to the latest if no option has been given.
    let ot =
        [(opts.parse, OutputTParse)
         (opts.collate, OutputTCollation)
         (opts.model, OutputTModel)
         (opts.flatten, OutputTFlatten)
         (opts.expand, OutputTExpand)
         (opts.semantics, OutputTSemantics)
         (opts.frame, OutputTFrame)
         (opts.termgen, OutputTTermGen)
         (opts.reify, OutputTReify)
         (opts.z3, OutputTZ3)]
        |> List.tryFind fst
    match ot with
    | Some (_, o) -> o
    | None -> OutputTSat

/// Runs Starling and outputs the results.
let starlingMain opts =
    let input = opts.input
    let human = opts.human
    let otype = otypeFromOpts opts

    let starlingR = runStarling input otype

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
