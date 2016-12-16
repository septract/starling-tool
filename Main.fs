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
open Starling.Core.Definer
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
open Starling.Core.Traversal
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
    /// Stop at symbolic proof translation.
    | SymProof
    /// Stop at SMT term elimination.
    | Eliminate
    /// Output the results of using SMT elimination as a proof, if possible.
    | SMTProof of Backends.Z3.Types.Request
    /// Run the MuZ3 backend (experimental), with the given request.
    | MuZ3 of Backends.MuZ3.Types.Request
    /// Run the HSF backend (experimental).
    | HSF
    /// Run the Grasshopper backend (experimental) 
    | Grasshopper 

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
       ("Emits the entire proof with symbolic variables.",
        Request.SymProof))
      ("eliminate",
       ("Stops Starling model generation at SMT elimination.",
        Request.Eliminate))
      ("smt-sat",
       ("Tries to prove the input using SMT, and returns the term results.",
        Request.SMTProof Backends.Z3.Types.Request.SatMap))
      ("smt-failures",
       ("Tries to prove the input using SMT, and returns the failures.",
        Request.SMTProof Backends.Z3.Types.Request.Failures))
      ("smt-allterms",
       ("Tries to prove the input using SMT, and returns detailed results.",
        Request.SMTProof Backends.Z3.Types.Request.AllTerms))
      ("smt-remaining",
       ("Proves as much as possible using SMT, returning the remaining proof.",
        Request.SMTProof Backends.Z3.Types.Request.RemainingSymBools))
      ("mutranslate",
       ("(EXPERIMENTAL: KNOWN TO BE UNSOUND) Generates a proof using MuZ3 and outputs the individual terms.",
        Request.MuZ3 Backends.MuZ3.Types.Request.Translate))
      ("mufix",
       ("(EXPERIMENTAL: KNOWN TO BE UNSOUND) Generates a proof using MuZ3 and outputs the fixed point.",
        Request.MuZ3 Backends.MuZ3.Types.Request.Fix))
      ("musat",
       ("(EXPERIMENTAL: KNOWN TO BE UNSOUND) Executes a proof using MuZ3 and reports the result.",
        Request.MuZ3 Backends.MuZ3.Types.Request.Sat))
      ("hsf",
       ("Outputs a proof in HSF format.",
        Request.HSF)) 
      ("grass",
       ("Outputs a proof in Grasshopper format.",
        Request.Grasshopper))]

/// Converts an optional -s stage name to a request item.
/// If none is given, the latest stage is selected.
let requestFromStage (ostage : string option) : Request option =
    let pickStage stageName = List.tryFind (fun (x, _) -> x = stageName) requestList

    (withDefault "smt-sat" ostage).ToLower()
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
    /// Stop at symbolic proof calculation.
    | SymProof of Model<SymProofTerm, FuncDefiner<BoolExpr<Sym<Var>> option>>
    /// Stop at SMT term elimination.
    | Eliminate of Backends.Z3.Types.ZModel
    (*
     * Proof backends
     *)
    /// Output the results of using SMT elimination as a proof, if possible.
    | SMTProof of Backends.Z3.Types.Response
    /// The result of MuZ3 backend processing.
    | MuZ3 of Backends.MuZ3.Types.Response
    /// The result of HSF processing.
    | HSF of Backends.Horn.Types.Horn list
    /// The results of Grasshopper 
    | Grasshopper of Backends.Grasshopper.Types.GrassModel


/// Pretty-prints a response.
let printResponse (mview : ModelView) : Response -> Doc =
    let printVModel paxiom m =
        printModelView
            paxiom
            (printViewDefiner
                (maybe (String "?") (printBoolExpr (printSym printVar))))
            mview m
    let printFModel paxiom m =
        printModelView paxiom
            (printFuncDefiner
                (maybe (String "?") (printBoolExpr (printSym printVar))))
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
    | SymProof m -> printUModel printSymProofTerm m
    | Eliminate m -> printUModel Backends.Z3.Pretty.printZTerm m
    | SMTProof z -> Backends.Z3.Pretty.printResponse mview z
    | MuZ3 z -> Backends.MuZ3.Pretty.printResponse mview z
    | HSF h -> Backends.Horn.Pretty.printHorns h
    | Grasshopper g -> Backends.Grasshopper.Pretty.printQuery g 


/// A top-level program error.
type Error =
    /// An error occurred in the frontend.
    | Frontend of Lang.Frontend.Error
    /// An error occurred in semantic translation.
    | Semantics of Semantics.Types.Error
    /// <summary>
    ///     An error occurred in the HSF backend.
    /// </summary>
    | HSF of Backends.Horn.Types.Error
    /// An error occurred in the Grasshopper backend. 
    | Grasshopper of Backends.Grasshopper.Types.Error
    /// <summary>
    ///     An error occurred in the MuZ3 backend.
    /// </summary>
    | MuZ3 of Backends.MuZ3.Types.Error
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
    | Traversal of TraversalError<Error>
    /// A stage was requested using the -s flag that does not exist.
    | BadStage
    /// A miscellaneous (internal) error has occurred.
    | Other of string

/// <summary>
///     Prints a top-level program error.
/// </summary>
/// <param name="err">The error to print.</param>
/// <returns>
///     A <see cref="Doc"/> representing <paramref name="err"/>.
/// </returns>
let rec printError (err : Error) : Doc =
    match err with
    | Frontend e -> Lang.Frontend.printError e
    | Semantics e -> Semantics.Pretty.printSemanticsError e
    | HSF e -> Backends.Horn.Pretty.printError e
    | MuZ3 e -> Backends.MuZ3.Pretty.printError e
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
    | Grasshopper e -> Backends.Grasshopper.Pretty.printError e 
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
    | Traversal err -> Core.Traversal.Pretty.printTraversalError printError err

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
      ///     The approximation mode to use.
      /// </summary>
      ApproxMode : ApproxMode
      /// <summary>
      ///     Whether SMT reduction is being suppressed.
      /// </summary>
      NoSMTReduce : bool
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
             Allows some symbolic terms to be discharged by SMT, but the \
             resulting proof may be incomplete.",
             fun ps -> { ps with ApproxMode = Approx } ))
          ("try-approx",
           ("As 'approx', but don't fail if a term cannot be approximated.\
             Instead, proceed for that term as if approximation was not\
             requested.",
             fun ps -> { ps with ApproxMode = TryApprox } ))
          ("no-smt-reduce",
           ("Don't remove SMT-solved proof terms before applying the backend.\n\
             This can speed up some solvers due to overconstraining the search \
             space.",
             fun ps -> { ps with NoSMTReduce = true } ))
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
        |> maybe (Seq.empty) Utils.parseOptionString
        |> Seq.toList
        |> Optimiser.Utils.parseOptimisationString

    let bp = backendParams ()
    let { ApproxMode = approxMode
          NoSMTReduce = noSMTReduce
          Reals = shouldUseRealsForInts } =
        config.backendOpts
        |> maybe (Seq.empty) Utils.parseOptionString
        |> Seq.fold
               (fun opts str ->
                    match (bp.TryFind str) with
                    | Some (_, f) -> f opts
                    | None ->
                        eprintfn "unknown backend param %s ignored (try 'list')"
                            str
                        opts)
               { ApproxMode = NoApprox; NoSMTReduce = false; Reals = false }

    // Shorthand for the various stages available.
    let hsf = bind (Backends.Horn.hsfModel >> mapMessages Error.HSF)
    let smt rq = lift (Backends.Z3.backend rq)
    let muz3 rq =
        bind (Backends.MuZ3.run shouldUseRealsForInts rq
              >> mapMessages Error.MuZ3)
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
    let grasshopper = 
        bind (Backends.Grasshopper.grassModel 
              >> mapMessages Error.Grasshopper) 

    // Prepares a model for insertion into a Horn clause solver, by trying to
    // throw away symbols and removing already-proven-by-Z3 clauses.
    let prepareForHorn =
        bind
            (fun model ->
                // If the user specified not to reduce, don't filter to SMT
                // failures.
                let nonProvenZTerms =
                    if noSMTReduce
                    then model.Axioms
                    else Backends.Z3.extractFailures model
                // TODO(CaptainHayashi): maybe don't lose information here.
                let nonProvenAxioms =
                    Map.map
                        (fun _ { Backends.Z3.Types.ZTerm.Original = a } -> a)
                        nonProvenZTerms
                let nonProvenModel = withAxioms nonProvenAxioms model
                // We can't have symbols in our view constraints, so strip them.
                let npmNoSymbolicConstraintsR =
                    Core.Instantiate.DefinerFilter.filterModelNonSymbolicConstraints
                        nonProvenModel
                mapMessages ModelFilterError npmNoSymbolicConstraintsR)

    let symproof : Result<Model<_, _>, Error> -> Result<Model<_, _>, Error> =
        bind (Core.Instantiate.Phase.run approxMode
              >> mapMessages Error.ModelFilterError)
    let eliminate : Result<Model<_, _>, Error> -> Result<Model<_, _>, Error>  =
        lift (Backends.Z3.runZ3OnModel shouldUseRealsForInts)

    let backend (m : Result<Backends.Z3.Types.ZModel, Error>) : Result<Response,Error>  =
        let phase op response =
            let time = System.Diagnostics.Stopwatch.StartNew()
            op m
            |>  (time.Stop(); (if config.times then printfn "Phase Backend; Elapsed: %dms" time.ElapsedMilliseconds); id)
            |> lift response

        match request with
        | Request.SMTProof rq -> phase (smt rq) Response.SMTProof
        // TODO: plug eliminate into HSF
        | Request.HSF         -> phase (prepareForHorn >> hsf) Response.HSF
        | Request.MuZ3 rq     -> phase (prepareForHorn >> muz3 rq) Response.MuZ3
        | Request.Grasshopper -> phase grasshopper Response.Grasshopper  
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
    ** phase  symproof       Request.SymProof       Response.SymProof
    ** phase  eliminate      Request.Eliminate      Response.Eliminate
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

    either
        (printOk pfn printError >> fun _ -> 0)
        (printErr printError >> fun _ -> 1)
        starlingR

[<EntryPoint>]
let main (argv : string[]) : int =
    match CommandLine.Parser.Default.ParseArguments<Options> argv with
    | :? Parsed<Options> as parsed -> mainWithOptions parsed.Value
    | :? NotParsed<Options> as notParsed ->
        2
    | _ ->
        printfn "parse result of unknown type"
        3


