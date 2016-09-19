/// <summary>
///     The Z3 backend.
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
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Instantiate
open Starling.Core.Z3


/// <summary>
///     Types for the Z3 backend, including errors.
/// </summary>
[<AutoOpen>]
module Types =
    // A Z3-reified term.
    type ZTerm = Term<Z3.BoolExpr, Z3.BoolExpr, Z3.BoolExpr>

    /// Type of requests to the Z3 backend.
    type Request =
        /// Only translate the term views; return `Response.Translate`.
        | Translate
        /// Translate and combine term Z3 expressions; return `Response.Combine`.
        | Combine
        /// Translate, combine, and run term Z3 expressions; return `Response.Sat`.
        | Sat

    /// <summary>
    ///     Type of responses from the Z3 backend.
    /// </summary>
    [<NoComparison>]
    type Response =
        /// <summary>
        ///     Output of the term translation step only.
        /// </summary>
        | Translate of Model<ZTerm, unit>
        /// <summary>
        ///     Output of the final Z3 terms only.
        /// </summary>
        | Combine of Model<Z3.BoolExpr, unit>
        /// <summary>
        ///     Output of satisfiability reports for the Z3 terms.
        /// </summary>
        | Sat of Map<string, Z3.Status>


/// <summary>
///     Pretty printers for the Z3 types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Z3.Pretty

    /// Pretty-prints a response.
    let printResponse mview =
        function
        | Response.Translate m ->
            printModelView
                (printTerm printZ3Exp printZ3Exp printZ3Exp)
                (fun _ -> Seq.empty)
                mview
                m
        | Response.Combine m ->
            printModelView
                printZ3Exp
                (fun _ -> Seq.empty)
                mview
                m
        | Response.Sat s ->
            printMap Inline String printSat s


/// <summary>
///     Functions for translating Starling elements into Z3.
/// </summary>
module Translator =
    open Starling.Core.Z3.Expr
    ///
    /// Combines the components of a reified term.
    let combineTerm reals (ctx: Z3.Context) ({Cmd = c; WPre = w; Goal = g} : CmdTerm<MBoolExpr, MBoolExpr, MBoolExpr>) =
        (* This is effectively asking Z3 to refute (c ^ w => g).
         *
         * This arranges to:
         *   - ¬(c^w => g) premise
         *   - ¬(¬(c^w) v g) def. =>
         *   - ((c^w) ^ ¬g) deMorgan
         *   - (c^w^¬g) associativity.
         *)
        boolToZ3 reals unmarkVar ctx (mkAnd [c.Semantics ; w; mkNot g] )

    /// Combines reified terms into a list of Z3 terms.
    let combineTerms reals ctx = mapAxioms (combineTerm reals ctx)


/// <summary>
///     Proof execution using Z3.
/// </summary>
module Run =
    /// Runs Z3 on a single term, given the context in `model`.
    let runTerm (ctx: Z3.Context) _ term =
        let solver = ctx.MkSimpleSolver()
        solver.Assert [| term |]
        solver.Check [||]

    /// Runs Z3 on a model.
    let run ctx = axioms >> Map.map (runTerm ctx)


/// Shorthand for the combination stage of the Z3 pipeline.
let combine reals = Translator.combineTerms reals
/// Shorthand for the satisfiability stage of the Z3 pipeline.
let sat = Run.run

/// <summary>
///     The Starling Z3 backend driver.
/// </summary>
/// <param name="reals">
///     Whether to use Real instead of Int.
///     This can be faster, but is slightly inaccurate.
/// </param>
/// <param name="req">
///     The request to handle.
/// </param>
/// <returns>
///     A function implementing the chosen Z3 backend process.
/// </returns>
let run reals req : Model<ProofTerm, unit> -> Response =
    use ctx = new Z3.Context()
    match req with
    | Request.Translate ->
        (mapAxioms (mapTerm (fun c -> Expr.boolToZ3 reals unmarkVar ctx c.Semantics)
                            (Expr.boolToZ3 reals unmarkVar ctx)
                            (Expr.boolToZ3 reals unmarkVar ctx)))
        >> Response.Translate
    | Request.Combine -> combine reals ctx >> Response.Combine
    | Request.Sat -> combine reals ctx >> sat ctx >> Response.Sat
