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
open Starling.Core.Command
open Starling.Core.Command.Pretty
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Pretty
open Starling.Core.Axiom
open Starling.Core.Axiom.Pretty


/// Command-line flags used in the Starling executable.
[<NoComparison>]
type Options =
    { [<Option(
            'r',
            HelpText =
                "Dump results in raw format instead of pretty-printing.")>]
      raw : bool
      [<Option(
            'R',
            HelpText =
                "(TEMPORARY) Use reals instead of ints in Z3 proofs.")>]
      reals : bool
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
      showModel : bool
      [<Option('O', HelpText = "Switches given optimisations on or off.")>]
      optimisers : string seq
      [<Option('v', HelpText = "Increases verbosity.")>]
      verbose : bool
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
    /// Run the MuZ3 backend (experimental), with the given request.
    | MuZ3 of Backends.MuZ3.Types.Request
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
                 ("mutranslate", Request.MuZ3 Backends.MuZ3.Types.Request.Translate)
                 ("mufix", Request.MuZ3 Backends.MuZ3.Types.Request.Fix)
                 ("musat", Request.MuZ3 Backends.MuZ3.Types.Request.Sat)
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
    | GraphOptimise of UVModel<Graph>
    /// Stop at graph axiomatisation.
    | Axiomatise of UVModel<Axiom<MGView, Command>>
    /// The result of goal-axiom-pair generation.
    | GoalAdd of UVModel<GoalAxiom>
    /// The result of term generation.
    | TermGen of UVModel<PTerm<MGView, OView>>
    /// The result of term reification.
    | Reify of UVModel<PTerm<MViewSet, OView>>
    /// The result of term flattening.
    | Flatten of UFModel<PTerm<MGView, MVFunc>>
    /// The result of semantic expansion.
    | Semantics of UFModel<STerm<MGView, MVFunc>>
    /// The result of term optimisation.
    | TermOptimise of UFModel<STerm<MGView, MVFunc>>
    /// The result of Z3 backend processing.
    | Z3 of Backends.Z3.Types.Response
    /// The result of MuZ3 backend processing.
    | MuZ3 of Backends.MuZ3.Types.Response
    /// The result of HSF processing.
    | HSF of Backends.Horn.Types.Horn list

/// Pretty-prints a response.
let printResponse mview =
    function
    | Frontend f -> Lang.Frontend.printResponse mview f
    | GraphOptimise g ->
        printUVModelView printGraph mview g
    | Axiomatise m ->
        printUVModelView (printAxiom printCommand printMGView) mview m
    | GoalAdd m ->
        printUVModelView printGoalAxiom mview m
    | TermGen m ->
        printUVModelView (printPTerm printMGView printOView) mview m
    | Reify m ->
        printUVModelView (printPTerm printMViewSet printOView) mview m
    | Flatten m ->
        printUFModelView (printPTerm printMGView printMVFunc) mview m
    | Semantics m ->
        printUFModelView (printSTerm printMGView printMVFunc) mview m
    | TermOptimise m ->
        printUFModelView (printSTerm printMGView printMVFunc) mview m
    | Z3 z -> Backends.Z3.Pretty.printResponse mview z
    | MuZ3 z -> Backends.MuZ3.Pretty.printResponse mview z
    | HSF h -> Backends.Horn.Pretty.printHorns h

/// A top-level program error.
type Error =
    /// An error occurred in the frontend.
    | Frontend of Lang.Frontend.Error
    /// An error occurred in semantic translation.
    | Semantics of Semantics.Types.Error
    /// An error occurred in the Z3 backend.
    | Z3 of Backends.Z3.Types.Error
    /// An error occurred in the HSF backend.
    | HSF of Backends.Horn.Types.Error
    /// <summary>
    ///     A backend required the model to be filtered for indefinite
    ///     and/or uninterpreted viewdefs, but the filter failed.
    /// </summary>
    | ModelFilterError of Core.Instantiate.Types.Error
    /// A stage was requested using the -s flag that does not exist.
    | BadStage
    /// A miscellaneous (internal) error has occurred.
    | Other of string

/// Prints a top-level program error.
let printError =
    function
    | Frontend e -> Lang.Frontend.printError e
    | Semantics e -> Semantics.Pretty.printSemanticsError e
    | Z3 e -> Backends.Z3.Pretty.printError e
    | HSF e -> Backends.Horn.Pretty.printHornError e
    | ModelFilterError e ->
        headed "View definitions are incompatible with this backend"
               [ Core.Instantiate.Pretty.printError e ]
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
let z3 reals rq = bind (Backends.Z3.run reals rq >> mapMessages Error.Z3)

/// Shorthand for the MuZ3 stage.
let muz3 reals rq = lift (Backends.MuZ3.run reals rq)

/// Shorthand for the frontend stage.
let frontend rq = Lang.Frontend.run rq >> mapMessages Error.Frontend

/// Shorthand for the graph optimise stage.
let graphOptimise optR optA verbose =
    // graphOptimise implies the full frontend has run.
    frontend Lang.Frontend.Request.Graph
    >> bind (function
             | Lang.Frontend.Response.Graph m -> m |> ok
             | _ -> Other "internal error: bad frontend response" |> fail)
    >> lift (Starling.Optimiser.Graph.optimise optR optA verbose)

/// Shorthand for the term optimise stage.
let termOptimise optR optA verbose =
    lift (Starling.Optimiser.Term.optimise optR optA verbose)

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
let axiomatise = lift Starling.Core.Graph.axiomatise

/// <summary>
///     Shorthand for the stage filtering a model to indefinite and
///     definite views.
/// </summary>
let filterIndefinite =
    bind (Core.Instantiate.ViewDefFilter.filterModelIndefinite
          >> mapMessages ModelFilterError)

/// <summary>
///     Shorthand for the stage filtering a model to definite views only.
/// </summary>
let filterDefinite =
    bind (Core.Instantiate.ViewDefFilter.filterModelDefinite
          >> mapMessages ModelFilterError)

/// <summary>
///     Runs a Starling request.
/// </summary>
/// <param name="optS">
///     The string governing optimiser overrides.
/// </param>
/// <param name="reals">
///     (TEMPORARY) Whether to use reals instead of ints in MuZ proofs.
/// </param>
/// <param name="verbose">
///     If true, dump some internal information to stderr.
/// </param>
/// <param name="request">
///     The Starling request to run.
/// </param>
/// <returns>
///     A function implementing the chosen Starling pipeline,
///     taking a file containing request input and returning a
///     <c>Result</c> over <c>Response</c> and <c>Error</c>.
/// </returns>
let runStarling optS reals verbose request =
    let optR, optA = Optimiser.Utils.parseOptString optS

    let failPhase = fun _ -> fail (Error.Other "Internal")
    let backend =
            match request with
            | Request.HSF     -> filterIndefinite >> hsf >> lift Response.HSF
            | Request.Z3 rq   -> filterDefinite >> z3 reals rq >> lift Response.Z3
            | Request.MuZ3 rq -> filterIndefinite >> muz3 reals rq >> lift Response.MuZ3
            | _               -> failPhase

    //Build a phase with
    //  op as what to do
    //  if request is test, then we output the results
    //  otherwise we continue with the rest of the phases.
    let phase op test output continuation = op >> if request = test then lift output else continuation

    // Left pipe is not right associative
    // so locally overload a right associative operator to be left pipe
    let ( ** ) = ( <| )

    if verbose
    then
        eprintfn "Z3 version: %s" (Microsoft.Z3.Version.ToString ())

    let graphOptimise = graphOptimise optR optA verbose
    let termOptimise = termOptimise optR optA verbose

    match request with
    | Request.Frontend rq -> frontend rq >> lift Response.Frontend
    | _ ->
        phase     graphOptimise  Request.GraphOptimise  Response.GraphOptimise
        ** phase  axiomatise     Request.Axiomatise     Response.Axiomatise
        ** phase  goalAdd        Request.GoalAdd        Response.GoalAdd
        ** phase  termGen        Request.TermGen        Response.TermGen
        ** phase  reify          Request.Reify          Response.Reify
        ** phase  flatten        Request.Flatten        Response.Flatten
        ** phase  semantics      Request.Semantics      Response.Semantics
        ** phase  termOptimise   Request.TermOptimise   Response.TermOptimise
        ** backend

/// Runs Starling with the given options, and outputs the results.
let mainWithOptions opts =
    let optS = Seq.toList opts.optimisers
    let verbose = opts.verbose
    let reals = opts.reals

    let starlingR =
        match (requestFromStage opts.stage) with
        | Some otype -> runStarling optS reals verbose otype opts.input
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
