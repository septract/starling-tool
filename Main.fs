/// Main module for the Starling executable.
module Main

open CommandLine
open Chessie.ErrorHandling

open Starling
open Starling.Utils
open Starling.Utils.Config
open Starling.Core.Pretty
open Starling.Core.Graph
open Starling.Core.Graph.Pretty
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Model.Pretty
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Pretty
open Starling.Core.Command
open Starling.Core.Command.Pretty
open Starling.Core.View
open Starling.Core.View.Pretty
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Pretty
open Starling.Core.Axiom
open Starling.Core.Axiom.Pretty


/// Enumeration of possible requests to Starling.
type Request =
    /// List all available requests.
    | List
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
    /// Output a fully-instantiated proof with symbols.
    | SymProof
    /// Output a fully-instantiated unstructured proof with symbols.
    | RawSymProof
    /// Output a fully-instantiated proof without symbols.
    | Proof
    /// Output a fully-instantiated unstructured proof without symbols.
    | RawProof
    /// Run the Z3 backend, with the given request.
    | SymZ3 of Backends.Z3.Types.Request
    /// Run the Z3 backend, with the given request.
    | Z3 of Backends.Z3.Types.Request
    /// Run the MuZ3 backend (experimental), with the given request.
    | MuZ3 of Backends.MuZ3.Types.Request
    /// Run the HSF backend (experimental).
    | HSF

/// Map of -s stage names to Request items.
let requestMap =
    Map.ofList
        [ ("list",
           ("Lists all available phases.",
            Request.List))
          ("parse",
           ("Parses and formats a Starling file with no further processing.",
            Request.Frontend Lang.Frontend.Request.Parse))
          ("collate",
           ("Stops Starling frontend processing at script collation.",
            Request.Frontend Lang.Frontend.Request.Collate))
          ("model",
           ("Stops Starling frontend processing at initial modelling.",
            Request.Frontend Lang.Frontend.Request.Model))
          ("guard",
           ("Stops Starling frontend processing at guarded view generation.",
            Request.Frontend Lang.Frontend.Request.Guard))
          ("graph",
           ("Outputs an unoptimised control-flow graph series.",
            Request.Frontend Lang.Frontend.Request.Graph))
          ("graphoptimise",
           ("Outputs an optimised control-flow graph series.",
            Request.GraphOptimise))
          ("axiomatise",
           ("Stops Starling model generation at graph axiomatisation.",
            Request.Axiomatise))
          ("goaladd",
           ("Stops Starling model generation at goal generation.",
            Request.GoalAdd))
          ("termgen",
           ("Stops Starling model generation at proof term generation.",
            Request.TermGen))
          ("reify",
           ("Stops Starling model generation at view reification.",
            Request.Reify))
          ("flatten",
           ("Stops Starling model generation at view flattening.",
            Request.Flatten))
          ("semantics",
           ("Stops Starling model generation at command semantics instantiation.",
            Request.Semantics))
          ("termoptimise",
           ("Stops Starling model generation at term optimisation.",
            Request.TermOptimise))
          ("symproof",
           ("Outputs a proof in Starling format, with all symbols intact.",
            Request.SymProof))
          ("rawsymproof",
           ("Outputs a definite proof in unstructured Starling format, with all symbols removed.",
            Request.RawSymProof))
          ("proof",
           ("Outputs a definite proof in Starling format, with all symbols removed.",
            Request.Proof))
          ("rawproof",
           ("Outputs a definite proof in unstructured Starling format, with all symbols removed.",
            Request.RawProof))
          ("z3",
           ("Outputs a definite proof in structured Z3/SMTLIB format.",
            Request.Z3 Backends.Z3.Types.Request.Translate))
          ("rawz3",
           ("Outputs a definite proof in unstructured Z3/SMTLIB format.",
            Request.Z3 Backends.Z3.Types.Request.Combine))
          ("sat",
           ("Executes a definite proof using Z3 and reports the result.",
            Request.Z3 Backends.Z3.Types.Request.Sat))
          ("symsat",
           ("Executes a symbolic proof using Z3 and reports failing clauses.",
            Request.SymZ3 Backends.Z3.Types.Request.Sat))
          ("mutranslate",
           ("Generates a proof using MuZ3 and outputs the individual terms.",
            Request.MuZ3 Backends.MuZ3.Types.Request.Translate))
          ("mufix",
           ("Generates a proof using MuZ3 and outputs the fixed point.",
            Request.MuZ3 Backends.MuZ3.Types.Request.Fix))
          ("musat",
           ("Executes a proof using MuZ3 and reports the result.",
            Request.MuZ3 Backends.MuZ3.Types.Request.Sat))
          ("hsf",
           ("Outputs a proof in HSF format.",
            Request.HSF)) ]

/// Converts an optional -s stage name to a request item.
/// If none is given, the latest stage is selected.
let requestFromStage (ostage : string option) =
    (withDefault "sat" ostage).ToLower()
    |> requestMap.TryFind
    |> Option.map snd

/// Type of possible outputs from a Starling run.
[<NoComparison>]
type Response =
    /// List all available requests.
    | List of Map<string, string>
    /// The result of frontend processing.
    | Frontend of Lang.Frontend.Response
    /// Stop at graph optimisation.
    | GraphOptimise of UVModel<Graph>
    /// Stop at graph axiomatisation.
    | Axiomatise of UVModel<Axiom<SVGView, Command>>
    /// The result of goal-axiom-pair generation.
    | GoalAdd of UVModel<GoalAxiom<Command>>
    /// The result of semantic expansion.
    | Semantics of UVModel<GoalAxiom<SMBoolExpr>>
    /// The result of term generation.
    | TermGen of UVModel<STerm<SMGView, OView>>
    /// The result of term reification.
    | Reify of UVModel<STerm<Set<GuardedSubview>, OView>>
    /// The result of term flattening.
    | Flatten of UFModel<STerm<SMGView, SMVFunc>>
    /// The result of term optimisation.
    | TermOptimise of UFModel<STerm<SMGView, SMVFunc>>
    /// Output a fully-instantiated symbolic proof.
    | SymProof of Model<SFTerm, unit>
    /// Output a fully-instantiated symbolic unstructured proof.
    | RawSymProof of Model<SMBoolExpr, unit>
    /// Output a fully-instantiated non-symbolic proof.
    | Proof of Model<FTerm, unit>
    /// Output a fully-instantiated non-symbolic unstructured proof.
    | RawProof of Model<MBoolExpr, unit>
    /// The result of Z3 backend processing.
    | Z3 of Backends.Z3.Types.Response
    /// The result of Z3 backend processing.
    | SymZ3 of Backends.Z3.Types.Response * Model<SFTerm, unit>
    /// The result of MuZ3 backend processing.
    | MuZ3 of Backends.MuZ3.Types.Response
    /// The result of HSF processing.
    | HSF of Backends.Horn.Types.Horn list


/// Pretty-prints a response.
let printResponse mview =
    function
    | List l -> printMap Indented String String l
    | Frontend f -> Lang.Frontend.printResponse mview f
    | GraphOptimise g ->
        printUVModelView printGraph mview g
    | Axiomatise m ->
        printUVModelView (printAxiom printSVGView printCommand) mview m
    | GoalAdd m ->
        printUVModelView (printGoalAxiom printCommand) mview m
    | Semantics m ->
        printUVModelView (printGoalAxiom printSMBoolExpr) mview m
    | TermGen m ->
        printUVModelView (printSTerm printSMGView printOView) mview m
    | Reify m ->
        printUVModelView (printSTerm printGuardedSubviewSet printOView) mview m
    | Flatten m ->
        printUFModelView (printSTerm printSMGView printSMVFunc) mview m
    | TermOptimise m ->
        printUFModelView (printSTerm printSMGView printSMVFunc) mview m
    | SymProof m ->
        printModelView
            (printTerm printSMBoolExpr printSMBoolExpr printSMBoolExpr)
            (fun _ -> Seq.empty)
            mview
            m
    | RawSymProof m ->
        printModelView
            Core.Symbolic.Pretty.printSMBoolExpr
            (fun _ -> Seq.empty)
            mview
            m
    | Proof m ->
        printModelView
            (printTerm
                 Core.Var.Pretty.printMBoolExpr
                 Core.Var.Pretty.printMBoolExpr
                 Core.Var.Pretty.printMBoolExpr)
            (fun _ -> Seq.empty)
            mview
            m
    | RawProof m ->
        printModelView
            Core.Var.Pretty.printMBoolExpr
            (fun _ -> Seq.empty)
            mview
            m
    | Z3 z -> Backends.Z3.Pretty.printResponse mview z
    | SymZ3 (z, m) ->
       vmerge (Backends.Z3.Pretty.printResponse mview z)
              (printModelView
                (printTerm printSMBoolExpr printSMBoolExpr printSMBoolExpr)
                (fun _ -> Seq.empty)
                mview
                m)
    | MuZ3 z -> Backends.MuZ3.Pretty.printResponse mview z
    | HSF h -> Backends.Horn.Pretty.printHorns h


/// A top-level program error.
type Error =
    /// An error occurred in the frontend.
    | Frontend of Lang.Frontend.Error
    /// An error occurred in semantic translation.
    | Semantics of Semantics.Types.Error
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

/// Shorthand for the raw proof output stage.
let rawproof
  (res : Result<Model<CTerm<Core.Expr.Types.BoolExpr<'a>>, 'b>, Error>)
  : Result<Model<Core.Expr.Types.BoolExpr<'a>, 'b>, Error> =
    lift
        (mapAxioms
             (fun { Cmd = c; WPre = w; Goal = g } ->
                  Core.Expr.mkImplies (Core.Expr.mkAnd2 c w) g))
        res


/// Shorthand for the symbolic proof output stage.
let symproof = bind (Core.Instantiate.Phase.run >> mapMessages Error.ModelFilterError)

/// Shorthand for the non-symbolic proof output stage.
let proof approx v =
    let aprC =
        if approx
        then
            Starling.Core.Command.SymRemove.removeSym
        else id

    let apr position =
        if approx
        then
            Core.TypeSystem.Mapper.mapBoolCtx
                Starling.Core.Symbolic.Queries.approx
                position
            >> snd
        else id

    let sub =
        Core.TypeSystem.Mapper.mapBoolCtx
            (tsfRemoveSym Core.Instantiate.Types.UnwantedSym)
            Core.Sub.Types.SubCtx.NoCtx
        >> snd

    let pos = Starling.Core.Sub.Position.positive
    let neg = Starling.Core.Sub.Position.negative

    bind
        (tryMapAxioms
             (tryMapTerm
                  (aprC >> (apr neg) >> sub >> lift Starling.Core.Expr.simp)
                  ((apr neg) >> sub >> lift Starling.Core.Expr.simp)
                  ((apr pos) >> sub >> lift Starling.Core.Expr.simp))
         >> mapMessages Error.ModelFilterError)
        v

/// Shorthand for the HSF stage.
let hsf = bind (Backends.Horn.hsfModel >> mapMessages Error.HSF)

/// Shorthand for the Z3 stage.
let z3 reals rq = lift (Backends.Z3.run reals rq)

/// Shorthand for the MuZ3 stage.
let muz3 reals rq = lift (Backends.MuZ3.run reals rq)

/// Shorthand for the frontend stage.
let frontend times rq = Lang.Frontend.run times rq Response.Frontend Error.Frontend

/// Shorthand for the graph optimise stage.
let graphOptimise opts =
    lift (fix <| Starling.Optimiser.Graph.optimise opts)

/// Shorthand for the term optimise stage.
let termOptimise opts =
    lift (fix <| Starling.Optimiser.Term.optimise opts)

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
///     Type of the backend parameter structure.
/// </summary>
type BackendParams =
    // TODO(CaptainHayashi): distribute into the target backends?
    { /// <summary>
      ///     Whether symbols are being approximated.
      /// </summary>
      Approx : bool
      /// <summary>
      ///     Whether reals are being substituted for integers in Z3 proofs.
      /// </summary>
      Reals : bool }

/// <summary>
///     Map of known backend parameters.
/// </summary>
let rec backendParams () =
    Map.ofList
        [ ("approx",
           ("Replace all symbols in a proof with their under-approximation.\n\
             Allows some symbol proofs to be run by the Z3 backend, but the \
             resulting proof may be incomplete.",
             fun ps -> { ps with Approx = true } ))
          ("reals",
           ("In Z3/muZ3 proofs, model integers as reals.\n\
             This may speed up the proof at the cost of soundness.",
             fun ps -> { ps with Reals = true } ))
          ("list",
           ("Lists all backend parameters.",
            fun ps ->
                eprintfn "Backend parameters:\n"
                Map.iter
                    (fun name (descr, _) -> eprintfn "%s: %s\n" name descr)
                    (backendParams ())
                eprintfn "--\n"
                ps)) ]

/// <summary>
///     Runs a Starling request.
/// </summary>
/// <param name="request">
///     The Starling request to run.
/// </param>
/// <returns>
///     A function implementing the chosen Starling pipeline,
///     taking a file containing request input and returning a
///     <c>Result</c> over <c>Response</c> and <c>Error</c>.
/// </returns>
let runStarling request =
    let config = config()

    let opts =
        config.optimisers
        |> Option.map Utils.parseOptionString
        |> withDefault (Seq.empty)
        |> Seq.toList
        |> Optimiser.Utils.parseOptString

    let bp = backendParams ()
    let { Approx = approx; Reals = reals } =
        config.backendOpts
        |> Option.map Utils.parseOptionString
        |> withDefault (Seq.empty)
        |> Seq.fold
               (fun opts str ->
                    match (bp.TryFind str) with
                    | Some (_, f) -> f opts
                    | None ->
                        eprintfn "unknown backend param %s ignored (try 'list')"
                            str
                        opts)
               { Approx = false; Reals = false }

    let backend m =
        let phase op response =
            let time = System.Diagnostics.Stopwatch.StartNew()
            op m
            |>  (time.Stop(); (if config.times then printfn "Phase Backend; Elapsed: %dms" time.ElapsedMilliseconds); id)
            |> lift response

        let maybeApprox =
            lift
                (if approx
                 then
                     mapAxioms
                         ((mapTerm
                               Starling.Core.Command.SymRemove.removeSym
                               id
                               id)
                          >> (Sub.subExprInDTerm
                                  Starling.Core.Symbolic.Queries.approx
                                  Starling.Core.Sub.Position.positive)
                          >> snd)
                 else id)


        // Magic function for unwrapping / wrapping Result types
        // TODO: make less horrible, e.g. by using some non-result-wrapped type from z3
        let tuplize f y = (y >>= fun x -> (lift (fun a -> (a,x)) (f y)) )

        match request with
        | Request.SymProof    -> phase symproof Response.SymProof
        | Request.RawSymProof -> phase (symproof >> rawproof) Response.RawSymProof
        | Request.Proof       -> phase (symproof >> proof approx) Response.Proof
        | Request.RawProof    -> phase (symproof >> proof approx >> rawproof) Response.RawProof
        | Request.Z3 rq       -> phase (symproof >> proof approx >> z3 reals rq) Response.Z3
        | Request.HSF         -> phase (filterIndefinite >> hsf) Response.HSF
        | Request.MuZ3 rq     -> phase (filterIndefinite >> muz3 reals rq) Response.MuZ3
        | Request.SymZ3 rq    -> phase (symproof >> (tuplize (proof approx >> z3 reals rq))) Response.SymZ3
        | _                   -> fail (Error.Other "Internal")

    //Build a phase with
    //  op as what to do
    //  if request is test, then we output the results
    //  otherwise we continue with the rest of the phases.
    let phase op test output continuation m =
        let time = System.Diagnostics.Stopwatch.StartNew()
        op m
        |> (time.Stop(); (if config.times then printfn "Phase %A; Elapsed: %dms" test time.ElapsedMilliseconds); id)
        |> if request = test then lift output else continuation

    // Left pipe is not right associative
    // so locally overload a right associative operator to be left pipe
    let ( ** ) = ( <| )

    if config.verbose
    then
        eprintfn "Z3 version: %s" (Microsoft.Z3.Version.ToString ())

    let graphOptimise = graphOptimise opts
    let termOptimise = termOptimise opts

    frontend config.times (match request with | Request.Frontend rq -> rq | _ -> Lang.Frontend.Request.Continuation)
    ** phase  graphOptimise  Request.GraphOptimise  Response.GraphOptimise
    ** phase  axiomatise     Request.Axiomatise     Response.Axiomatise
    ** phase  goalAdd        Request.GoalAdd        Response.GoalAdd
    ** phase  semantics      Request.Semantics      Response.Semantics
    ** phase  termGen        Request.TermGen        Response.TermGen
    ** phase  reify          Request.Reify          Response.Reify
    ** phase  flatten        Request.Flatten        Response.Flatten
    ** phase  termOptimise   Request.TermOptimise   Response.TermOptimise
    ** backend

/// Runs Starling with the given options, and outputs the results.
let mainWithOptions options =
    _configRef := options
    let config = config ()

    let starlingR =
        match (requestFromStage config.stage) with
        // Handle pseudo-requests here, as it's cleaner than doing so in
        // runStarling.
        | Some Request.List ->
            ok (Response.List (Map.map (fun _ -> fst) requestMap))
        | Some otype -> runStarling otype config.input
        | None -> fail Error.BadStage

    let mview =
        match config.term, config.showModel with
        | Some i, _ -> Term i
        | None, false -> Terms
        | _ -> Model

    let pfn =
        if config.raw then (sprintf "%A" >> String)
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
