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
open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Core.Instantiate
open Starling.Core.Sub
open Starling.Core.Symbolic
open Starling.Core.TypeSystem
open Starling.Core.Z3


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
          Original: Core.Instantiate.Types.FinalTerm

          /// <summary>
          ///     The above as a Boolean expression with all non-Z3-native parts
          ///     converted to symbols.
          /// </summary>
          SymBool: Term<BoolExpr<Sym<MarkedVar>>,
                        BoolExpr<Sym<MarkedVar>>,
                        BoolExpr<Sym<MarkedVar>>>

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
        | SatMap of Map<string, Z3.Status option>
        /// <summary>
        ///     Collect the failures from SMT elimination in expanded form.
        /// </summary>
        | Failures of Map<string, ZTerm>
        /// <summary>
        ///     Show every proof term, its derivation, and its Z3 status.
        /// </summary>
        | AllTerms of Map<string, ZTerm>
        /// <summary>
        ///     Show the remaining proof obligations as symbolic Boolean
        ///     expressions.
        /// </summary>
        | RemainingSymBools of Map<string, BoolExpr<Sym<MarkedVar>>>


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

    /// Pretty-prints a partial satisfiability result.
    let printMaybeSat (sat : Z3.Status option) : Doc =
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
                    (printGView (printSym printMarkedVar))
                    (printVFunc (printSym printMarkedVar))
                    zterm.Original ]
              headed "Symbolic conversion" <|
                [ printTerm
                    (printBoolExpr (printSym printMarkedVar))
                    (printBoolExpr (printSym printMarkedVar))
                    (printBoolExpr (printSym printMarkedVar))
                    zterm.SymBool ]
              headed "Z3 expansion" <|
                [ withDefault (String "None available")
                    (Option.map (printTerm printZ3Exp printZ3Exp printZ3Exp)
                        zterm.Z3) ]
              colonSep [ String "Status"; printMaybeSat zterm.Status ] ]

    /// <summary>
    ///     Pretty-prints a <see cref="ZTerm"/> as a failure report.
    /// </summary>
    /// <param ref="name">The name of the proof term to print.</param>
    /// <param ref="term">The <see cref="ZTerm"/> to print.</param>
    /// <returns>
    ///     The <see cref="Doc"/> corresponding to <paramref name="term"/>.
    /// </returns>
    let printFailure (name : string) (term : ZTerm) : Doc =
        let genpred p =
            errorInfo (headed "which was translated into" [ p ])
        cmdHeaded (errorContext (String name) <+> printMaybeSat term.Status)
            [ cmdHeaded (error (String "Could not prove that this command"))
                [ printCommand term.Original.Cmd.Cmd
                  genpred <| printBoolExpr (printSym printMarkedVar) term.Original.Cmd.Semantics ]
              cmdHeaded (error (String "under the weakest precondition"))
                [ printGView (printSym printMarkedVar) term.Original.WPre
                  genpred <| printBoolExpr (printSym printMarkedVar) term.SymBool.WPre ]
              cmdHeaded (error (String "establishes"))
                [ printVFunc (printSym printMarkedVar) term.Original.Goal
                  genpred <| printBoolExpr (printSym printMarkedVar) term.SymBool.Goal ]
            ]

    /// Pretty-prints a response.
    let printResponse (mview : ModelView) (response : Response) : Doc =
        match response with
        | SatMap map -> printMap Inline String printMaybeSat map
        | Failures map ->
            if Map.isEmpty map
            then success (String "No proof failures")
            else
                cmdHeaded (error (String "Proof failures"))
                    (Seq.map (uncurry printFailure) (Map.toSeq map))
        | AllTerms map -> printMap Indented String printZTerm map
        | RemainingSymBools map ->
            printMap Indented String (printBoolExpr (printSym printMarkedVar))
                map

/// Runs Z3 on a single term.
let runTerm (ctx: Z3.Context) term =
    let solver = ctx.MkSimpleSolver ()
    solver.Assert [| term |]
    solver.Check [||]

/// <summary>
///     Uses Z3 to mark some proof terms as eliminated.
///     If approximates were enabled, Z3 will prove them instead of the
///     symbolic proof terms, allowing it to eliminate tautological
/// </summary>
/// <param name="reals">
///     Whether to use Real instead of Int.
///     This can be faster, but is slightly inaccurate.
/// </param>
/// <param name="model">The model to translate and part-solve.</param>
/// <returns>
///     A model with proof terms marked up with their SMT solver results.
/// </returns>
let eliminate (reals : bool)
  (model : Model<SymProofTerm, FuncDefiner<BoolExpr<Sym<Var>> option>>)
  : ZModel =
    use ctx = new Z3.Context ()

    // Try to remove symbols from boolean expressions: don't error if we can't
    let removeSym bexp =
        let _, res = Mapper.mapBoolCtx (tsfRemoveSym id) NoCtx bexp
        okOption res

    (* If the user asked for approximation, then, instead of taking the
       SymBool as the source of Z3 queries, use the approximation.  This will
       result in a stronger, but perhaps more SMT-solvable, proof. *)
    let zsource term selectSym selectNoSym =
        // Yay, monomorphism!
        match term.Approx with
        | Some a -> Some (selectNoSym a)
        | None -> removeSym (selectSym term.SymBool)

    let z3Term (term : SymProofTerm) : ZTerm =
        // We can only run Z3 if the symbool has no symbols in it.
        let cmdO = zsource term (fun t -> t.Cmd) (fun t -> t.Cmd)
        let wpreO = zsource term (fun t -> t.WPre) (fun t -> t.WPre)
        let goalO = zsource term (fun t -> t.Goal) (fun t -> t.Goal)

        let z3, status =
            match cmdO, wpreO, goalO with
            | Some cmd, Some wpre, Some goal ->
                (* This is mainly for auditing purposes: we don't use it in the
                   proof.  Instead, we combine cmd, wpre, and goal _before_
                   converting to Z3. *)
                let z =
                    { Cmd = Expr.boolToZ3 reals unmarkVar ctx cmd
                      WPre = Expr.boolToZ3 reals unmarkVar ctx wpre
                      Goal = Expr.boolToZ3 reals unmarkVar ctx goal }

                (* This is effectively asking Z3 to refute (c ^ w => g).
                 *
                 * This arranges to:
                 *   - ¬(c^w => g) premise
                 *   - ¬(¬(c^w) v g) def. =>
                 *   - ((c^w) ^ ¬g) deMorgan
                 *   - (c^w^¬g) associativity.
                 *)
                let combined =
                    Expr.boolToZ3 reals unmarkVar ctx
                        (mkAnd [ cmd; wpre; mkNot goal ])

                // This bit actually runs Z3 on the term.
                let s = runTerm ctx combined
                Some z, Some s
            | _ -> None, None

        { Original = term.Original
          SymBool = term.SymBool
          Z3 = z3
          Status = status }

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
let backend (request : Request) (model : ZModel)
  : Response =
    // TODO(CaptainHayashi): reject if any deferred checks.
    match request with
    | Request.SatMap -> SatMap (extractSats model)
    | Request.AllTerms -> AllTerms (model.Axioms)
    | Request.Failures -> Failures (extractFailures model)
    | Request.RemainingSymBools ->
        RemainingSymBools
            (Map.map
                (fun _ v ->
                    mkAnd
                        [ v.SymBool.Cmd; v.SymBool.WPre; mkNot v.SymBool.Goal ])
                model.Axioms)
