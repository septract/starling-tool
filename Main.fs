/// Main module for the Starling executable.
module Main

open CommandLine
open Chessie.ErrorHandling

open Starling
open Starling.Core.Pretty
open Starling.Core.Graph
open Starling.Core.Graph.Pretty
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Model.Pretty
open Starling.Core.Axiom
open Starling.Core.Axiom.Pretty


/// Command-line flags used in the Starling executable.
type Options =
    { [<Option(
            'r',
            HelpText =
                "Dump results in raw format instead of pretty-printing.")>]
      raw : bool
      [<Option(
            's',
            HelpText =
                "The stage at which Starling should stop and output.")>]
      stage : string option
      [<Option(
            't',
            HelpText =
                "Show specific axiom or term in term-refinement stages.")>]
      term : string option
      [<Option('m', HelpText = "Show full model in term-refinement stages.")>]
      showModel: bool
      [<Option('O', HelpText = "Perform no optimisation stages.")>]
      noOptimise : bool
      [<Value(
            0,
            MetaName = "input",
            HelpText =
                "The file to load (omit, or supply -, for standard input).")>]
      input : string option }

/// Enumeration of possible requests to Starling.
type Request =
    /// Run the language frontend only, with the given request.
    | Frontend of Lang.Frontend.Request
    /// Stop at graph optimisation.
    | GraphOptimise
    /// Stop at graph axiomatisation.
    | Axiomatise
    /// Stop at goalAdd-axiom-pair generation.
    | GoalAdd
    /// Stop at term generation.
    | TermGen
    /// Stop at view reification.
    | Reify
    /// Stop at term flattening.
    | Flatten
    /// Stop at semantic transformation.
    | Semantics
    /// Stop at term optimisation.
    | TermOptimise
    /// Run the Z3 backend, with the given request.
    | Z3 of Backends.Z3.Types.Request
    /// Run the HSF backend (experimental).
    | HSF

/// Map of -s stage names to Request items.
let requestMap =
    Map.ofList [ ("parse", Request.Frontend Lang.Frontend.Request.Parse)
                 ("collate", Request.Frontend Lang.Frontend.Request.Collate)
                 ("model", Request.Frontend Lang.Frontend.Request.Model)
                 ("guard", Request.Frontend Lang.Frontend.Request.Guard)
                 ("graph", Request.Frontend Lang.Frontend.Request.Graph)
                 ("graphOptimise", Request.GraphOptimise)
                 ("axiomatise", Request.Axiomatise)
                 ("goalAdd", Request.GoalAdd)
                 ("termgen", Request.TermGen)
                 ("reify", Request.Reify)
                 ("flatten", Request.Flatten)
                 ("semantics", Request.Semantics)
                 ("termOptimise", Request.TermOptimise)
                 ("reifyZ3", Request.Z3 Backends.Z3.Types.Request.Translate)
                 ("z3", Request.Z3 Backends.Z3.Types.Request.Combine)
                 ("sat", Request.Z3 Backends.Z3.Types.Request.Sat)
                 ("hsf", Request.HSF) ]

/// Converts an optional -s stage name to a request item.
/// If none is given, the latest stage is selected.
let requestFromStage ostage =
    Map.tryFind (withDefault "sat" ostage) requestMap

/// Type of possible outputs from a Starling run.
[<NoComparison>]
type Response =
    /// The result of frontend processing.
    | Frontend of Lang.Frontend.Response
    /// Stop at graph optimisation.
    | GraphOptimise of Model<Graph, DView>
    /// Stop at graph axiomatisation.
    | Axiomatise of Model<Axiom<GView, VFunc>, DView>
    /// The result of goal-axiom-pair generation.
    | GoalAdd of Model<GoalAxiom, DView>
    /// The result of term generation.
    | TermGen of Model<PTerm<GView, View>, DView>
    /// The result of term reification.
    | Reify of Model<PTerm<ViewSet, View>, DView>
    /// The result of term flattening.
    | Flatten of Model<PTerm<GView, VFunc>, DFunc>
    /// The result of semantic expansion.
    | Semantics of Model<STerm<GView, VFunc>, DFunc>
    /// The result of term optimisation.
    | TermOptimise of Model<STerm<GView, VFunc>, DFunc>
    /// The result of Z3 backend processing.
    | Z3 of Backends.Z3.Types.Response
    /// The result of HSF processing.
    | HSF of Backends.Horn.Types.Horn list

/// Pretty-prints a response.
let printResponse mview =
    function
    | Frontend f -> Lang.Frontend.printResponse mview f
    | GraphOptimise g ->
        printModelView
            mview
            printGraph
            printDView
            g
    | Axiomatise m ->
        printModelView
            mview
            (printPAxiom printGView)
            printDView
            m
    | GoalAdd m ->
        printModelView
            mview
            printGoalAxiom printDView m
    | TermGen m ->
        printModelView
            mview
            (printPTerm printGView printView)
            printDView
            m
    | Reify m ->
        printModelView
            mview
            (printPTerm printViewSet printView)
            printDView
            m
    | Flatten m ->
        printModelView
            mview
            (printPTerm printGView printVFunc)
            printDFunc
            m
    | Semantics m ->
        printModelView
            mview
            (printSTerm printGView printVFunc)
            printDFunc
            m
    | TermOptimise m ->
        printModelView
            mview
            (printSTerm printGView printVFunc)
            printDFunc
            m
    | Z3 z -> Backends.Z3.Pretty.printResponse mview z
    | HSF h -> Backends.Horn.Pretty.printHorns h

/// A top-level program error.
type Error =
    /// An error occurred in the frontend.
    | Frontend of Lang.Frontend.Error
    /// An error occurred in axiomatisation.
    | Axiomatise of Core.Graph.Types.Error
    /// An error occurred in graph optimisation.
    | GraphOptimise of Core.Graph.Types.Error
    /// An error occurred in semantic translation.
    | Semantics of Semantics.Types.Error
    /// An error occurred in the Z3 backend.
    | Z3 of Backends.Z3.Types.Error
    /// An error occurred in the HSF backend.
    | HSF of Backends.Horn.Types.Error
    /// A stage was requested using the -s flag that does not exist.
    | BadStage
    /// A miscellaneous (internal) error has occurred.
    | Other of string

/// Prints a top-level program error.
let printError =
    function
    | Frontend e -> Lang.Frontend.printError e
    | Axiomatise e -> Core.Graph.Pretty.printError e
    | GraphOptimise e -> Core.Graph.Pretty.printError e
    | Semantics e -> Semantics.Pretty.printSemanticsError e
    | Z3 e -> Backends.Z3.Pretty.printError e
    | HSF e -> Backends.Horn.Pretty.printHornError e
    | BadStage ->
        colonSep [ String "Bad stage"
                   String "try"
                   requestMap
                   |> Map.toSeq
                   |> Seq.map (fst >> String)
                   |> commaSep ]
    | Other e -> String e

/// Prints an ok result to stdout.
let printOk pOk pBad =
    pairMap pOk pBad
    >> function
       | (ok, []) -> ok
       | (ok, ws) -> vsep [ ok
                            VSkip
                            Separator
                            VSkip
                            headed "Warnings" ws ]
    >> print
    >> printfn "%s"

/// Prints an err result to stderr.
let printErr pBad =
    pBad >> headed "Errors" >> print >> eprintfn "%s"

/// Pretty-prints a Chessie result, given printers for the successful
/// case and failure messages.
let printResult pOk pBad =
    either (printOk pOk pBad) (printErr pBad)

/// Shorthand for the HSF stage.
let hsf = bind (Backends.Horn.hsfModel >> mapMessages Error.HSF)

/// Shorthand for the Z3 stage.
let z3 rq = bind (Backends.Z3.run rq >> mapMessages Error.Z3)

/// Shorthand for the graph optimise stage.
let graphOptimise = bind (Starling.Optimiser.Graph.optimise
                          >> mapMessages Error.GraphOptimise)

/// Shorthand for the term optimise stage.
let termOptimise = lift Starling.Optimiser.Term.optimise

/// Shorthand for the flattening stage.
let flatten = lift Starling.Flattener.flatten

/// Shorthand for the reify stage.
let reify = lift Starling.Reifier.reify

/// Shorthand for the term generation stage.
let termGen = lift Starling.TermGen.termGen

/// Shorthand for the goal adding stage.
let goalAdd = lift Starling.Core.Axiom.goalAdd

/// Shorthand for the semantics stage.
let semantics = bind (Starling.Semantics.translate
                      >> mapMessages Error.Semantics)

/// Shorthand for the axiomatisation stage.
let axiomatise = bind (Starling.Core.Graph.axiomatise
                       >> mapMessages Error.Axiomatise)

/// Shorthand for the frontend stage.
let frontend rq = Lang.Frontend.run rq >> mapMessages Error.Frontend

/// Shorthand for the full frontend stage.
let model =
    frontend Lang.Frontend.Request.Graph
    >> bind (function
             | Lang.Frontend.Response.Graph m -> m |> ok
             | _ -> Other "internal error: bad frontend response" |> fail)

/// Runs the Starling request at argument 2 on the file named by argument 3.
/// If missing, we read from stdin.
/// Argument 1 turns optimisation on if true.
let runStarling opt =
    let maybeGraphOptimise = if opt then graphOptimise else id
    let maybeTermOptimise = if opt then termOptimise else id

    function
    | Request.Frontend rq -> frontend rq >> lift Response.Frontend
    | Request.GraphOptimise ->
        model
        >> maybeGraphOptimise
        >> lift Response.GraphOptimise
    | Request.Axiomatise ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> lift Response.Axiomatise
    | Request.GoalAdd ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> lift Response.GoalAdd
    | Request.TermGen ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> lift Response.TermGen
    | Request.Reify ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> reify
        >> lift Response.Reify
    | Request.Flatten ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> reify
        >> flatten
        >> lift Response.Flatten
    | Request.Semantics ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> reify
        >> flatten
        >> semantics
        >> lift Response.Semantics
    | Request.TermOptimise ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> reify
        >> flatten
        >> semantics
        >> maybeTermOptimise
        >> lift Response.TermOptimise
    | Request.Z3 rq ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> reify
        >> flatten
        >> semantics
        >> maybeTermOptimise
        >> z3 rq
        >> lift Response.Z3
    | Request.HSF ->
        model
        >> maybeGraphOptimise
        >> axiomatise
        >> goalAdd
        >> termGen
        >> reify
        >> flatten
        >> semantics
        >> maybeTermOptimise
        >> hsf
        >> lift Response.HSF

/// Runs Starling with the given options, and outputs the results.
let mainWithOptions opts =
    let optimise = not opts.noOptimise

    let starlingR =
        match (requestFromStage opts.stage) with
        | Some otype -> runStarling optimise otype opts.input
        | None -> fail Error.BadStage

    let mview =
        match opts.term, opts.showModel with
        | Some i, _ -> Term i
        | None, false -> Terms
        | _ -> Model

    let pfn =
        if opts.raw then (sprintf "%A" >> String)
                    else printResponse mview
    printResult pfn (List.map printError) starlingR
    0

[<EntryPoint>]
let main argv =
    match CommandLine.Parser.Default.ParseArguments<Options> argv with
    | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value
    | :? NotParsed<Options> as notParsed ->
        2
    | _ ->
        printfn "parse result of unknown type"
        3
