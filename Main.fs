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
open Starling.Core.Expr
open Starling.Core.Expr.Pretty
open Starling.Core.Var
open Starling.Core.Var.Pretty
open Starling.Core.Model
open Starling.Core.Model.Pretty
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Pretty
open Starling.Semantics
open Starling.Semantics.Pretty
open Starling.Core.Instantiate
open Starling.Core.Instantiate.Pretty
open Starling.Core.Command
open Starling.Core.Command.Pretty
open Starling.Core.Sub
open Starling.Core.View
open Starling.Core.View.Pretty
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
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
    /// Stop at iterator lowering.
    | IterLower
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
let requestList : (string * (string * Request)) list =
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
      ("iterlower",
       ("Stops Starling model generation at iterator flattening.",
        Request.IterLower))
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
let requestFromStage (ostage : string option) : Request option =
    let pickStage stageName = List.tryFind (fun (x, _) -> x = stageName) requestList

    (withDefault "sat" ostage).ToLower()
    |> pickStage
    |> Option.map (snd >> snd)


/// Type of possible outputs from a Starling run.
[<NoComparison>]
type Response =
    /// List all available requests.
    | List of string list
    /// The result of frontend processing.
    | Frontend of Lang.Frontend.Response
    /// Stop at graph optimisation.
    | GraphOptimise of Model<Graph, ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// Stop at graph axiomatisation.
    | Axiomatise of Model<Axiom<IteratedGView<Sym<Var>>, Command>,
                          ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of goal-axiom-pair generation.
    | GoalAdd of Model<GoalAxiom<Command>, ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of semantic expansion.
    | Semantics of Model<GoalAxiom<CommandSemantics<SMBoolExpr>>, ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of term generation.
    | TermGen of Model<CmdTerm<SMBoolExpr, IteratedGView<Sym<MarkedVar>>, IteratedOView>,
                       ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of term reification.
    | Reify of Model<CmdTerm<SMBoolExpr, Set<GuardedIteratedSubview>, IteratedOView>,
                     ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of term generation.
    | IterLower of Model<CmdTerm<SMBoolExpr, Set<GuardedSubview>, OView>,
                         ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of term flattening.
    | Flatten of Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                       FuncDefiner<BoolExpr<Sym<Var>> option>>
    /// The result of term optimisation.
    | TermOptimise of Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                            FuncDefiner<BoolExpr<Sym<Var>> option>>
    /// Output a fully-instantiated symbolic proof.
    | SymProof of Model<SymProofTerm, unit>
    /// Output a fully-instantiated symbolic unstructured proof.
    | RawSymProof of Model<SMBoolExpr, unit>
    /// Output a fully-instantiated non-symbolic proof.
    | Proof of Model<ProofTerm, unit>
    /// Output a fully-instantiated non-symbolic unstructured proof.
    | RawProof of Model<MBoolExpr, unit>
    /// The result of Z3 backend processing.
    | Z3 of Backends.Z3.Types.Response
    /// The result of Z3 backend processing.
    | SymZ3 of Backends.Z3.Types.Response * Model<SymProofTerm, unit>
    /// The result of MuZ3 backend processing.
    | MuZ3 of Backends.MuZ3.Types.Response
    /// The result of HSF processing.
    | HSF of Backends.Horn.Types.Horn list


/// Pretty-prints a response.
let printResponse (mview : ModelView) : Response -> Doc =
    let printVModel paxiom m =
        printModelView
            paxiom
            (printViewDefiner
                (Option.map (printBoolExpr (printSym printVar))
                 >> withDefault (String "?")))
            mview m
    let printFModel paxiom m =
        printModelView paxiom
            (printFuncDefiner
                (Option.map (printBoolExpr (printSym printVar))
                 >> withDefault (String "?")))
            mview m
    let printUModel paxiom m =
        printModelView paxiom (fun _ -> Seq.empty) mview m

    function
    | List l -> printList String l
    | Frontend f -> Lang.Frontend.printResponse mview f
    | GraphOptimise g -> printVModel printGraph g
    | Axiomatise m -> printVModel (printAxiom printIteratedSVGView printCommand) m
    | GoalAdd m -> printVModel (printGoalAxiom printCommand) m
    | Semantics m -> printVModel (printGoalAxiom (printCommandSemantics printSMBoolExpr)) m
    | TermGen m ->
        printVModel
            (printCmdTerm
                printSMBoolExpr
                (printIteratedGView (printSym printMarkedVar))
                printIteratedOView) m
    | Reify m -> printVModel (printCmdTerm printSMBoolExpr (printSubviewSet printGuardedIteratedSubview) printIteratedOView) m
    | IterLower m -> printVModel (printCmdTerm printSMBoolExpr (printSubviewSet printGuardedSubview) printOView) m
    | Flatten m -> printFModel (printCmdTerm printSMBoolExpr printSMGView printSMVFunc) m
    | TermOptimise m -> printFModel (printCmdTerm printSMBoolExpr printSMGView printSMVFunc) m
    | SymProof m ->
        printUModel
            printSymProofTerm
            m
    | RawSymProof m ->
        printUModel Core.Symbolic.Pretty.printSMBoolExpr m
    | Proof m ->
        printUModel
            printProofTerm
            m
    | RawProof m ->
        printUModel Core.Var.Pretty.printMBoolExpr m
    | Z3 z -> Backends.Z3.Pretty.printResponse mview z
    | SymZ3 (z, m) ->
       vmerge (Backends.Z3.Pretty.printResponse mview z)
              (printUModel
                printSymProofTerm
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
    ///     An error occurred during reifying.
    /// </summary>
    | Reify of Reifier.Types.Error
    /// <summary>
    ///     An error occurred during term generation.
    /// </summary>
    | TermGen of TermGen.Error
    /// <summary>
    ///     An error occurred during the graph optimiser pass.
    /// </summary>
    | GraphOptimiser of Optimiser.Types.GraphOptError
    /// <summary>
    ///     An error occurred during the term optimiser pass.
    /// </summary>
    | TermOptimiser of Optimiser.Types.TermOptError
    /// <summary>
    ///     An error occurred during iterator lowering.
    /// </summary>
    | IterLowerError of TermGen.Iter.Error
    /// <summary>
    ///     A backend required the model to be filtered for indefinite
    ///     and/or uninterpreted viewdefs, but the filter failed.
    /// </summary>
    | ModelFilterError of Core.Instantiate.Types.Error
    /// <summary>
    ///     A main-level traversal went belly-up.
    /// </summary>
    | Traversal of SubError<Error>
    /// A stage was requested using the -s flag that does not exist.
    | BadStage
    /// A miscellaneous (internal) error has occurred.
    | Other of string

/// Prints a top-level program error.
let rec printError (err : Error) : Doc =
    match err with
    | Frontend e -> Lang.Frontend.printError e
    | Semantics e -> Semantics.Pretty.printSemanticsError e
    | HSF e -> Backends.Horn.Pretty.printHornError e
    | GraphOptimiser e ->
        headed "Graph optimiser failed"
               [ Optimiser.Pretty.printGraphOptError e ]
    | TermOptimiser e ->
        headed "Term optimiser failed"
               [ Optimiser.Pretty.printTermOptError e ]
    | Reify e ->
        headed "Reification failed"
               [ Reifier.Pretty.printError e ]
    | TermGen e ->
        headed "Term generation failed"
               [ TermGen.Pretty.printError e ]
    | IterLowerError e ->
        headed "Iterator lowering failed"
               [ TermGen.Iter.printError e ]
    | ModelFilterError e ->
        headed "View definitions are incompatible with this backend"
               [ Core.Instantiate.Pretty.printError e ]
    | BadStage ->
        colonSep [ String "Bad stage"
                   String "try"
                   requestList
                   |> List.map (fst >> String)
                   |> commaSep ]
    | Other e -> String e
    | Traversal err -> Core.Sub.Pretty.printSubError printError err

/// Prints an ok result to stdout.
let printOk (pOk : 'Ok -> Doc) (pBad : 'Warn -> Doc)
  : ('Ok * 'Warn list) -> unit =
    pairMap pOk (List.map pBad)
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
let printErr (pBad : 'Error -> Doc) : 'Error list -> unit =
    List.map pBad >> headed "Errors" >> print >> eprintfn "%s"

/// Pretty-prints a Chessie result, given printers for the successful
/// case and failure messages.
let printResult (pOk : 'Ok -> Doc) (pBad : 'Error -> Doc)
  : Result<'Ok, 'Error> -> unit =
    either (printOk pOk pBad) (printErr pBad)

/// Shorthand for the raw proof output stage.
/// TODO: Keep around the CommandSemantics types longer
let rawproof
  (res : Result<Model<Term<CommandSemantics<BoolExpr<'a>>, BoolExpr<'a>, BoolExpr<'a>>, unit>, Error>)
  : Result<Model<BoolExpr<'a>, unit>, Error> =
    lift
        (mapAxioms
             (fun { Cmd = c; WPre = w; Goal = g } ->
                  Core.Expr.mkImplies (Core.Expr.mkAnd2 c.Semantics w) g))
        res

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
let rec backendParams ()
  : Map<string, string * (BackendParams -> BackendParams)> =
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
let runStarling (request : Request)
  : string option -> Result<Response, Error> =

    let config = config()

    let opts =
        config.optimisers
        |> Option.map Utils.parseOptionString
        |> withDefault (Seq.empty)
        |> Seq.toList
        |> Optimiser.Utils.parseOptimisationString

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

    // Shorthand for the various stages available.
    let hsf = bind (Backends.Horn.hsfModel >> mapMessages Error.HSF)
    let z3 reals rq = lift (Backends.Z3.run reals rq)
    let muz3 reals rq = lift (Backends.MuZ3.run reals rq)
    let frontend times rq =
        Lang.Frontend.run times rq Response.Frontend Error.Frontend
    let graphOptimise =
        (fix (bind (Starling.Optimiser.Graph.optimise opts
                    >> mapMessages Error.GraphOptimiser)))
    let termOptimise =
        (fix (bind (Starling.Optimiser.Term.optimise opts
                    >> mapMessages Error.TermOptimiser)))
    let flatten = lift Starling.Flattener.flatten
    let reify = bind (Starling.Reifier.reify >> mapMessages Error.Reify)
    let termGen = bind (Starling.TermGen.termGen >> mapMessages Error.TermGen)
    let iterLower =
        bind (Starling.TermGen.Iter.flatten >> mapMessages IterLowerError)
    let goalAdd = lift Starling.Core.Axiom.goalAdd
    let semantics =
        bind (Starling.Semantics.translate
              >> mapMessages Error.Semantics)
    let axiomatise = lift Starling.Core.Graph.axiomatise
    let filterIndefinite =
        bind (Core.Instantiate.DefinerFilter.filterModelIndefinite
              >> mapMessages ModelFilterError)
    let symproof =
        bind (Core.Instantiate.Phase.run
              >> mapMessages Error.ModelFilterError)

    // TODO: keep around CommandSemantics longer
    let proof v =
        let aprC =
            if approx then Starling.Core.Command.SymRemove.removeSym else id

        // approx returns SubError<unit>, we need to convert to SubError<Error>
        let toError (err: SubError<unit>) : Error =
            // This is horrible, but F# makes us do it
            Error.Traversal
                (match err with
                 | Inner x -> failwith "unreachable [unit error for sub]"
                 | BadType (x, y) -> BadType (x, y)
                 | ContextMismatch (x, y) -> ContextMismatch (x, y))

        let apr (position : TraversalContext)
          : BoolExpr<_> -> Result<BoolExpr<_>, Error> =
            if approx
            then
                (boolSubVars Starling.Core.Symbolic.Queries.approx)
                    position
                >> lift snd
                >> mapMessages toError
            else ok

        let sub =
            withoutContext (removeSymFromBoolExpr UnwantedSym)
            >> mapMessages
                (Core.Instantiate.Types.Traversal >> ModelFilterError)

        let ssub = sub >> lift simp

        let pos = Starling.Core.Sub.Context.positive
        let neg = Starling.Core.Sub.Context.negative

        let mapCmd cmdSemantics =
            let strippedCmd = aprC cmdSemantics.Semantics
            let negApproxedCmdResult = apr neg strippedCmd
            let symRemovedCmdResult = bind ssub negApproxedCmdResult
            lift (fun bexpr -> { Semantics = bexpr; Cmd = cmdSemantics.Cmd })
                symRemovedCmdResult

        bind
            (tryMapAxioms
                 (tryMapTerm
                      mapCmd
                      ((apr neg) >> bind ssub)
                      ((apr pos) >> bind ssub)))
            v

    let backend m =
        let phase op response =
            let time = System.Diagnostics.Stopwatch.StartNew()
            op m
            |>  (time.Stop(); (if config.times then printfn "Phase Backend; Elapsed: %dms" time.ElapsedMilliseconds); id)
            |> lift response

        let maybeApprox =
            let stripCommand =
                (mapTerm
                    Starling.Core.Command.SymRemove.removeSym
                    id
                    id)

            let approxTerm =
                (liftTraversalOverTerm
                    (liftTraversalToExprSrc
                        Starling.Core.Symbolic.Queries.approx))
                    Starling.Core.Sub.Context.positive
                >> lift snd

            lift
                (if approx
                 then tryMapAxioms (stripCommand >> approxTerm)
                 else ok)


        // Magic function for unwrapping / wrapping Result types
        // TODO: make less horrible, e.g. by using some non-result-wrapped type from z3
        let tuplize f y = (y >>= fun x -> (lift (fun a -> (a,x)) (f y)) )

        match request with
        | Request.SymProof    -> phase symproof Response.SymProof
        | Request.RawSymProof -> phase (symproof >> rawproof) Response.RawSymProof
        | Request.Proof       -> phase (symproof >> proof) Response.Proof
        | Request.RawProof    -> phase (symproof >> proof >> rawproof) Response.RawProof
        | Request.Z3 rq       -> phase (symproof >> proof >> z3 reals rq) Response.Z3
        | Request.HSF         -> phase (filterIndefinite >> hsf) Response.HSF
        | Request.MuZ3 rq     -> phase (filterIndefinite >> muz3 reals rq) Response.MuZ3
        | Request.SymZ3 rq    -> phase (symproof >> (tuplize (proof >> z3 reals rq))) Response.SymZ3
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

    frontend config.times (match request with | Request.Frontend rq -> rq | _ -> Lang.Frontend.Request.Continuation)
    ** phase  graphOptimise  Request.GraphOptimise  Response.GraphOptimise
    ** phase  axiomatise     Request.Axiomatise     Response.Axiomatise
    ** phase  goalAdd        Request.GoalAdd        Response.GoalAdd
    ** phase  semantics      Request.Semantics      Response.Semantics
    ** phase  termGen        Request.TermGen        Response.TermGen
    ** phase  reify          Request.Reify          Response.Reify
    ** phase  iterLower      Request.IterLower      Response.IterLower
    ** phase  flatten        Request.Flatten        Response.Flatten
    ** phase  termOptimise   Request.TermOptimise   Response.TermOptimise
    ** backend

/// Runs Starling with the given options, and outputs the results.
let mainWithOptions (options : Options) : int =
    _configRef := options
    let config = config ()

    let starlingR =
        match (requestFromStage config.stage) with
        // Handle pseudo-requests here, as it's cleaner than doing so in
        // runStarling.
        | Some Request.List ->
            ok (Response.List (List.map fst requestList))
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
    printResult pfn printError starlingR
    0

[<EntryPoint>]
let main (argv : string[]) : int =
    match CommandLine.Parser.Default.ParseArguments<Options> argv with
    | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value
    | :? NotParsed<Options> as notParsed ->
        2
    | _ ->
        printfn "parse result of unknown type"
        3
