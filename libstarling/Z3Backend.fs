/// <summary>
///     The Z3 term eliminator.
///
///     <para>
///         This converts Starling proof terms into fully interpreted
///         negated implications, and uses Z3 as a SMT solver to check
///         the satisfiability of those terms one by one.
///     </para>
///     <para>
///         The Z3 backend is relatively stable, fast, and can accept a
///         large amount of Starling features, but does not support
///         indefinite view constraints or placeholder views.  This
///         means it is best for checking existing Starling proofs.
///     </para>
/// </summary>
module Starling.Backends.Z3

open Microsoft
open Starling
open Starling.Utils
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Core.Instantiate
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Z3
open Starling.Reifier


/// <summary>
///     Types for the Z3 backend, including errors.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A term combining a fully preprocessed Starling term and its Z3
    ///     equivalent.
    /// </summary>
    type ZTerm =
        { /// <summary>
          ///     The original, fully preprocessed Starling term.
          /// <summary>
          Original: Flattener.FlatTerm<Sym<MarkedVar>>

          /// <summary>
          ///     The above as a Boolean expression with all non-Z3-native parts
          ///     converted to symbols.
          /// </summary>
          SymBool: Core.Instantiate.Types.BoolTerm<Sym<MarkedVar>>

          /// <summary>
          ///     The Z3-reified equivalent, which may be optional if the
          ///     original term could not be converted into Z3.
          /// </summary>
          Z3: Term<Z3.BoolExpr, Z3.BoolExpr, Z3.BoolExpr> option

          /// <summary>
          ///     The proof status of this term.
          /// </summary>
          Status: Z3.Status option }

    /// <summary>
    ///     Type of models coming out of the Z3 prover.
    /// </summary>
    type ZModel = Model<ZTerm, FuncDefiner<BoolExpr<Sym<Var>> option>>

    /// <summary>
    ///     Type of requests to the Z3 backend.
    /// </summary>
    type Request =
        /// <summary>
        ///     Collect the results of SMT elimination in 'name: status' form.
        ///     <para>
        ///         This used to be the default output style, and is kept around
        ///         for regression tests.
        ///     </para>
        /// </summary>
        | SatMap
        /// <summary>
        ///     Collect the failures from SMT elimination in expanded form.
        /// </summary>
        | Failures
        /// <summary>
        ///     Show every proof term, its derivation, and its Z3 status.
        /// </summary>
        | AllTerms
        /// <summary>
        ///     Show the remaining proof obligations as symbolic Boolean
        ///     expressions.
        /// </summary>
        | RemainingSymBools

    /// <summary>
    ///     Type of responses from the Z3 backend.
    /// </summary>
    [<NoComparison>]
    type Response =
        /// <summary>
        ///     Collect the results of SMT elimination in 'name: status' form.
        ///     <para>
        ///         This used to be the default output style, and is kept around
        ///         for regression tests.
        ///     </para>
        /// </summary>
        | SatMap of sats : Map<string, Z3.Status option>
                  * failedChecks : DeferredCheck list
        /// <summary>
        ///     Collect the failures from SMT elimination in expanded form.
        /// </summary>
        | Failures of failedTerms : Map<string, ZTerm>
                    * failedChecks : DeferredCheck list
        /// <summary>
        ///     Show every proof term, its derivation, and its Z3 status.
        /// </summary>
        | AllTerms of terms : Map<string, ZTerm>
                    * failedChecks : DeferredCheck list
        /// <summary>
        ///     Show the remaining proof obligations as symbolic Boolean
        ///     expressions.
        /// </summary>
        | RemainingSymBools of terms : Map<string, BoolExpr<Sym<MarkedVar>>>
                          *    failedChecks : DeferredCheck list


/// <summary>
///     Pretty printers for the Z3 types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.GuardedView.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Instantiate.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.Z3.Pretty
    open Starling.Flattener
    open Starling.Reifier.Pretty

    /// Pretty-prints a partial satisfiability result.
    let private printMaybeSat (sat : Z3.Status option) : Doc =
        match sat with
        | None -> warning (String "not SMT solvable")
        | Some s -> printSat s

    /// <summary>
    ///     Pretty-prints a ZTerm.
    /// </summary>
    /// <param name="zterm">The <see cref="ZTerm"/> to pretty-print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> capturing <paramref name="zterm"/>.
    /// </returns>
    let printZTerm (zterm : ZTerm) : Doc =
        vsep
            [ headed "Original term" <|
                [ printCmdTerm
                    (printBoolExpr (printSym printMarkedVar))
                    (printReified (printGView (printSym printMarkedVar)))
                    (printFlattened (printVFunc (printSym printMarkedVar)))
                    zterm.Original ]
              headed "After instantiation" <|
                [ printTerm
                    (printBoolExpr (printSym printMarkedVar))
                    (printBoolExpr (printSym printMarkedVar))
                    (printBoolExpr (printSym printMarkedVar))
                    zterm.SymBool ]
              headed "Z3 expansion" <|
                [ maybe
                    (String "None available")
                    (printTerm printZ3Exp printZ3Exp printZ3Exp)
                    zterm.Z3 ]
              colonSep [ String "Status"; printMaybeSat zterm.Status ] ]

    /// <summary>
    ///     Configuration for formatting the output of the Z3 backend.
    /// </summary>
    type ViewConfig =
        { /// <summary>
          ///     Whether to emit the reified weakest precondition in
          ///     proof failures.
          /// </summary>
          ShowReifiedWPre : bool
          /// <summary>
          ///     Whether to emit the flattened goal in proof failures.
          /// </summary>
          ShowFlattenedGoal : bool
          /// <summary>
          ///     Whether to emit the backend translations in proof failures.
          /// </summary>
          ShowBackendTranslation : bool
          /// <summary>
          ///     Whether to show all iterators in printed views.
          /// </summary>
          ShowAllIterators : bool }

        /// <summary>
        ///     Pretty-prints a <see cref="ZTerm"/> as a failure report.
        /// </summary>
        /// <param name="name">The name of the proof term to print.</param>
        /// <param name="term">The <see cref="ZTerm"/> to print.</param>
        /// <returns>
        ///     The pair of <see cref="Doc"/>s corresponding to
        ///     <paramref name="term"/>'s failure header and body.
        /// </returns>
        member private vconf.PrintFailure (name : string) (term : ZTerm)
          : Doc * Doc =
            let piter =
                if vconf.ShowAllIterators
                then printIntExpr
                else printExprIterator

            let fmtViewList (l : Doc list) : Doc =
                if l.IsEmpty then String "the invariant" else vsep l

            let printWPre =
                let pvar = printSym printMarkedVar
                fmtViewList << printIteratedGViewAsListWith pvar (piter pvar)
            
            let printGoal (g : Core.View.Types.IteratedOView) : Doc =
                fmtViewList
                    (printIteratedOViewAsListWith
                        (piter (printSym printMarkedVar))
                        g)

            let backendTranslation b =
                seq {
                    if vconf.ShowBackendTranslation
                    then
                        let p = printBoolExpr (printSym printMarkedVar) b
                        yield errorInfo (headed "which was translated into" [ p ])
                }

            let wpreStanza =
                seq {
                    yield printWPre term.Original.WPre.Original

                    if vconf.ShowReifiedWPre then
                        yield
                            errorInfo
                                (headed "which was reified into"
                                    [ printGView (printSym printMarkedVar) term.Original.WPre.Reified ])

                    yield! backendTranslation term.SymBool.WPre
                }

            let goalStanza =
                seq {
                    yield printGoal term.Original.Goal.Original

                    if vconf.ShowFlattenedGoal then
                        yield
                            errorInfo
                                (headed "which was flattened into"
                                    [ printVFunc (printSym printMarkedVar)
                                        term.Original.Goal.Flattened ])

                    yield! backendTranslation term.SymBool.Goal
                }

            (* Show a more friendly body if the command is empty, ie. this is a
               semantic entailment rather than a command step. *)
            let cmd = term.Original.Cmd
            let body =
                if cmd.Cmd.IsEmpty
                then
                    [ errHeaded "Could not prove that the view" wpreStanza
                      errHeaded "semantically entails" goalStanza ]
                else
                    let cmdStanza =
                        seq {
                            yield printCommand term.Original.Cmd.Cmd
                            yield! backendTranslation term.Original.Cmd.Semantics
                        }

                    [ errHeaded "Could not prove that this command" cmdStanza
                      errHeaded "under the weakest precondition" wpreStanza
                      errHeaded "establishes" goalStanza ]

            (errorContext (String name) <+> printMaybeSat term.Status, vsep body)

        /// Pretty-prints a response.
        member vconf.PrintResponse (mview : ModelView) (response : Response) : Doc =
            // Add deferred checks to a response if and only if there are some.
            let attachChecks doc deferredChecks =
                match deferredChecks with
                | [] -> doc
                | xs ->
                    vsep
                        [ doc
                          errHeaded "These sanity checks could not be established"
                            (Seq.map printDeferredCheck xs)]

            match response with
            | SatMap (map, dcs) ->
                let mapDoc = printMap Inline String printMaybeSat map
                attachChecks mapDoc dcs
            | Failures (map, dcs) ->
                let mapDoc =
                    if Map.isEmpty map
                    then successStr "No proof failures"
                    else
                        errHeaded "Proof failures"
                            [ printAssoc Indented
                                 (Seq.map (uncurry vconf.PrintFailure)
                                     (Map.toSeq map)) ]
                attachChecks mapDoc dcs
            | AllTerms (map, dcs) ->
                let mapDoc = printMap Indented String printZTerm map
                attachChecks mapDoc dcs
            | RemainingSymBools (map, dcs) ->
                let mapDoc =
                    printMap Indented String (printBoolExpr (printSym printMarkedVar))
                        map
                attachChecks mapDoc dcs

    /// <summary>
    ///     Creates an initial Z3 view config struct.
    /// </summary>
    /// <returns>
    ///     An initial Z3 view config struct.
    /// </returns>
    let initialViewConfig () : ViewConfig =
        { ShowBackendTranslation = false
          ShowReifiedWPre = false
          ShowFlattenedGoal = false
          ShowAllIterators = false }

/// <summary>
///     Uses Z3 to mark some proof terms as eliminated.
///     If approximates were enabled, Z3 will prove them instead of the
///     symbolic proof terms, allowing it to eliminate tautological
/// </summary>
/// <param name="shouldUseRealsForInts">
///     Whether to use Real instead of Int.
///     This can be faster, but is slightly inaccurate.
/// </param>
/// <param name="model">The model to translate and part-solve.</param>
/// <returns>
///     A model with proof terms marked up with their SMT solver results.
/// </returns>
let runZ3OnModel (shouldUseRealsForInts : bool)
  (model : Model<SymProofTerm, FuncDefiner<BoolExpr<Sym<Var>> option>>)
  : ZModel =
    use ctx = new Z3.Context ()

    // Save us from having to supply all of these arguments every time.
    // TODO(CaptainHayashi): subtypes?
    let toZ3 b = Expr.boolToZ3 shouldUseRealsForInts unmarkVar ctx (mkTypedSub normalRec b)

    (* Try to remove symbols from boolean expressions.
       Suppress the Chessie error that happens if we can't, because in that case
       we just return a 'Z3 can't prove this' result. *)
    let removeSym bexp =
        // TODO(CaptainHayashi): subtypes?
        let bexpT = mkTypedSub normalRec bexp

        let result = mapTraversal (removeSymFromBoolExpr ignore) bexpT
        okOption result

    let z3Term (term : SymProofTerm) : ZTerm =
        (* If the user asked for approximation, then, instead of taking the
           SymBool as the source of Z3 queries, use the approximation.  This
           will result in a stronger, but perhaps more SMT-solvable, proof.

           Otherwise, try to remove all symbols from the symbool, and fail
           the Z3 proof if we can't. *)
        let { SymBool = symbool; Approx = approx } = term
        let cmdO  = maybe (removeSym symbool.Cmd)  (fun t -> Some t.Cmd)  approx
        let wpreO = maybe (removeSym symbool.WPre) (fun t -> Some t.WPre) approx
        let goalO = maybe (removeSym symbool.Goal) (fun t -> Some t.Goal) approx

        // First, populate the term without Z3 results.
        let zTermWithNoZ3 =
            { Original = term.Original
              SymBool = term.SymBool
              Z3 = None
              Status = None }

        // Now, see if we can fill them in.
        match cmdO, wpreO, goalO with
        | Some cmd, Some wpre, Some goal ->
            (* This is mainly for auditing purposes: we don't use it in the
               proof.  Instead, we combine cmd, wpre, and goal _before_
               converting to Z3. *)
            let z = { Cmd = toZ3 cmd; WPre = toZ3 wpre; Goal = toZ3 goal }

            (* This is effectively asking Z3 to refute (c ^ w => g).
             *
             * This arranges to:
             *   - ¬(c^w => g) premise
             *   - ¬(¬(c^w) v g) def. =>
             *   - ((c^w) ^ ¬g) deMorgan
             *   - (c^w^¬g) associativity.
             *)
            let combined = toZ3 (mkAnd [ cmd; wpre; mkNot goal ])

            // This bit actually runs Z3 on the term.
            let s = Starling.Core.Z3.Run.runTerm ctx combined

            { zTermWithNoZ3 with Z3 = Some z; Status = Some s }
        | _ -> zTermWithNoZ3

    mapAxioms z3Term model

/// <summary>
///     Extracts the satisfiability results from a system of
///     <see cref="ZTerm"/>s inside a model.
/// </summary>
/// <param name="model">The model to convert.</param>
/// <returns>
///     The satisfiability results, as a map from term names to Z3 statuses.
/// </returns>
let extractSats (model : ZModel) : Map<string, Z3.Status option> =
    let zterms = model.Axioms
    Map.map (fun _ v -> v.Status) zterms

/// <summary>
///     Extracts the proof failures from a system of
///     <see cref="ZTerm"/>s inside a model.
/// </summary>
/// <param name="model">The model to convert.</param>
/// <returns>
///     The map of <see cref="ZTerm"/>s that failed SMT solving.
/// </returns>
let extractFailures (model : ZModel) : Map<string, ZTerm> =
    let axseq = Map.toSeq model.Axioms
    let failseq =
        // Remember: we're trying to prove _unsat_ here.
        Seq.filter (fun (_, v) -> v.Status <> Some Z3.Status.UNSATISFIABLE)
            axseq
    Map.ofSeq failseq

/// <summary>
///     Uses the SMT eliminator as a proof backend.
/// </summary>
/// <param name="reals">
///     Whether to use Real instead of Int.
///     This can be faster, but is slightly inaccurate.
/// </param>
/// <param name="request">The backend request to implement.</param>
/// <param name="model">The model after SMT elimination.</param>
/// <returns>
///     A model with proof terms marked up with their SMT solver results.
/// </returns>
let backend (request : Request) (model : ZModel) : Response =
    let dcs = model.DeferredChecks

    match request with
    | Request.SatMap -> SatMap (extractSats model, dcs)
    | Request.AllTerms -> AllTerms (model.Axioms, dcs)
    | Request.Failures -> Failures (extractFailures model, dcs)
    | Request.RemainingSymBools ->
        RemainingSymBools
            (Map.map
                (fun _ v ->
                    mkAnd
                        [ v.SymBool.Cmd; v.SymBool.WPre; mkNot v.SymBool.Goal ])
                (extractFailures model),
             dcs)
