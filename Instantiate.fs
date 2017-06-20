/// <summary>
///     Func instantiation.
///
///     <para>
///         Starling has multiple stages during which we need to look up a
///         func in a list mapping funcs to Boolean expressions, and
///         substitute the func's arguments for the parameters in that Boolean
///         expression.
///     </para>
///     <para>
///         This is the resposibility of <c>Starling.Core.Instantiate</c>,
///         which contains the function <c>instantiate</c> for this
///         purpose.
///      </para>
/// </summary>
module Starling.Core.Instantiate

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Model
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.TypeSystem
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
open Starling.Reifier


/// <summary>
///     Types used in func instantiation.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     Type of terms going into instantiation.
    /// </summary>
    type FinalTerm =
        CmdTerm<BoolExpr<Sym<MarkedVar>>,
                Reified<GView<Sym<MarkedVar>>>,
                Func<Expr<Sym<MarkedVar>>>>

    /// <summary>
    ///     Type of models going into instantiation.
    /// </summary>
    type FinalModel = Model<FinalTerm, FuncDefiner<Sym<Var>>>

    /// <summary>
    ///     Type of Chessie errors arising from Instantiate.
    /// </summary>
    type Error =
        /// <summary>
        ///     An error occurred during func lookup.
        /// </summary>
        | BadFuncLookup of func : VFunc<Sym<MarkedVar>> * err : Definer.Error
        /// <summary>
        ///     We were given an indefinite constraint when trying to
        ///     assert that all constraints are definite.
        /// </summary>
        | IndefiniteConstraint of view: DFunc
        /// <summary>
        ///     We found a symbolic variable somewhere we didn't expect
        ///     one.
        /// </summary>
        | UnwantedVarSym of sym: Symbolic<Expr<Sym<Var>>>
        /// <summary>
        ///     We found a symbolic marked-variable somewhere we didn't expect
        ///     one.
        /// </summary>
        | UnwantedMarkedVarSym of sym: Symbolic<Expr<Sym<MarkedVar>>>
        /// <summary>
        ///     We tried to substitute parameters, but one parameter was free
        ///     (not bound to an expression) somehow.
        /// </summary>
        | FreeVarInSub of param: TypedVar
        /// <summary>
        ///     An error occurred during traversal.
        ///     This error may contain nested instantiation errors!
        /// </summary>
        | Traversal of TraversalError<Error>

    /// Terms in a Proof are boolean expression pre/post conditions with Command's
    type SymProofTerm =
        { /// <summary>
          ///    The proof term before symbolic conversion.
          /// </summary>
          Original: FinalTerm
          /// <summary>
          ///     The proof term after symbolic conversion.
          /// </summary>
          SymBool: Term<SMBoolExpr, SMBoolExpr, SMBoolExpr>
          /// <summary>
          ///     An approximate of the proof term with all symbols removed.
          ///     Only appears if approximation was requested.
          /// </summary>
          Approx : Term<MBoolExpr, MBoolExpr, MBoolExpr> option }

    /// Terms in a Proof are over boolean expressions
    type ProofTerm = CmdTerm<MBoolExpr, MBoolExpr, MBoolExpr>

    /// <summary>
    ///     The approximation mode.
    /// </summary>
    type ApproxMode =
        | /// <summary>Don't approximate at all.</summary>
          NoApprox
        | /// <summary>
          ///     Approximate, and ignore any failures.
          /// </summary>
          TryApprox
        | /// <summary>
          ///     Approximate, but fail if approximations are impossible.
          /// </summary>
          Approx

/// <summary>
///     Pretty printers used in func instantiation.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.GuardedView.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.View.Pretty
    open Starling.Reifier.Pretty

    /// Pretty-prints instantiation errors.
    let rec printError : Error -> Doc =
        function
        | BadFuncLookup (func, err) ->
            wrapped "resolution of func"
                (printVFunc (printSym printMarkedVar) func)
                (Starling.Core.Definer.Pretty.printError err)
        | IndefiniteConstraint (view) ->
            fmt "indefinite 'constraint {0} -> ?' not allowed here"
                [ printDFunc view ]
        | UnwantedVarSym sym ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            fmt "encountered uninterpreted symbol {0}"
                [ printSymbolic (printExpr (printSym printVar)) sym ]
        | UnwantedMarkedVarSym sym ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            fmt "encountered uninterpreted symbol {0}"
                [ printSymbolic (printExpr (printSym printMarkedVar)) sym ]
        | FreeVarInSub var ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            error
                (hsep
                    [ String "parameter '"
                      printTypedVar var
                      String "' has no substitution" ])
        | Traversal err -> Traversal.Pretty.printTraversalError printError err

    let printSymProofTerm (sterm : SymProofTerm) : Doc =
        vsep
            [ headed "Original term" <|
                [ printCmdTerm
                    (printBoolExpr (printSym printMarkedVar))
                    (printReified (printGView (printSym printMarkedVar)))
                    (printVFunc (printSym printMarkedVar))
                    sterm.Original ]
              headed "After instantiation" <|
                [ printTerm
                    (printBoolExpr (printSym printMarkedVar))
                    (printBoolExpr (printSym printMarkedVar))
                    (printBoolExpr (printSym printMarkedVar))
                    sterm.SymBool ]
              (match sterm.Approx with
               | None -> String "No approximation requested"
               | Some a ->
                headed "Approximate" <|
                    [ printTerm
                        (printBoolExpr printMarkedVar)
                        (printBoolExpr printMarkedVar)
                        (printBoolExpr printMarkedVar)
                        a ]) ]

    let printProofTerm : ProofTerm -> Doc =
        printCmdTerm printMBoolExpr printMBoolExpr printMBoolExpr


/// <summary>
///     Produces a <c>VSubFun</c> that substitutes the arguments of
///     <c>vfunc</c> for their parameters in <c>dfunc</c>, over
///     symbolic variables.
///
///     <para>
///         The function takes a pair of hooks for transforming various
///         parts of the substitution function, because it is used
///         for generating <c>VSubFun</c>s for both <c>MarkedVar</c>s
///         and <c>Sym</c>s.
///     </para>
/// </summary>
/// <param name="vfunc">
///     The func providing the arguments to substitute.
/// </param>
/// <param name="dfunc">
///     The <c>DFunc</c> into which we are substituting.
/// </param>
/// <typeparam name="Var">The type of context variables.</typeparam>
/// <returns>
///     A <see cref="Traversal"/> performing the above substitutions.
/// </returns>
let paramSubFun
  (vfunc : VFunc<Sym<MarkedVar>>)
  (dfunc : DFunc)
  : Traversal<TypedVar, Expr<Sym<MarkedVar>>, Error, 'Var> =
    let dpars = dfunc.Params
    let fpars = vfunc.Params
    let pmap = Map.ofSeq (Seq.map2 (fun par up -> valueOf par, up) dpars fpars)

    ignoreContext
        (function
         | WithType (var, vtype) as v ->
            match pmap.TryFind var with
            | Some expr when typesCompatible vtype (typeOf expr) -> ok expr
            | Some expr -> fail (Inner (BadFuncLookup (vfunc, TypeMismatch (v, typeOf expr))))
            | None -> fail (Inner (FreeVarInSub v)))

/// <summary>
///     Look up <c>func</c> in <c>_arg1</c>, and instantiate the
///     resulting Boolean expression, substituting <c>func.Params</c>
///     for the parameters in the expression.
/// </summary>
/// <param name="definer">
///     The <c>Definer</c> whose definition for <c>func</c> is to be
///     instantiated.
/// </param>
/// <param name="vfunc">
///     The <c>VFunc</c> whose arguments are to be substituted into
///     its definition in <c>_arg1</c>.
/// </param>
/// <returns>
///     The instantiation of <c>func</c> as an <c>Option</c>al
///     symbolic marked Boolean expression wrapped inside a Chessie result.
/// </returns>
let instantiate
  (definer : FuncDefiner<BoolExpr<Sym<Var>>>)
  (vfunc : VFunc<Sym<MarkedVar>>)
  : Result<BoolExpr<Sym<MarkedVar>> option, Error> =
    // TODO(CaptainHayashi): this symbolic code is horrific.

    let dfuncResult =
        wrapMessages BadFuncLookup
            (flip FuncDefiner.lookupWithTypeCheck definer) vfunc

    let subInTypedSym dfunc =
        tliftToTypedSymVarSrc (paramSubFun vfunc dfunc)
    let subInBool dfunc = tliftToBoolSrc (subInTypedSym dfunc)

    let result =
        bind
            (function
             | None -> ok None
             | Some (dfunc, defn) ->
                // Definitions have no extended type
                lift Some (mapTraversal (subInBool dfunc) (normalBool defn)))
            (mapMessages Inner dfuncResult)

    mapMessages Traversal result

/// <summary>
///     Partitions a <see cref="FuncDefiner"/> into a definite
///     definer and an indefinite definer.
/// </summary>
/// <param name="definer">
///     The definer to partition.
/// </param>
/// <returns>
///     A pair of definers: one gives definite definitions; the other
///     maps each indefinite definition to unit.
/// </returns>
let partitionDefiner
  (definer : FuncDefiner<SVBoolExpr option>)
  : (FuncDefiner<SVBoolExpr> * FuncDefiner<unit>) =
    definer
    |> FuncDefiner.toSeq
    |> Seq.fold
         (fun (defs, indefs) (func, def) ->
              match def with
              | Some d -> ((func, d)::defs, indefs)
              | None -> (defs, (func, ())::indefs))
         ([], [])
    |> pairMap FuncDefiner.ofSeq FuncDefiner.ofSeq

/// <summary>
///     Functions for definer filtering.
/// </summary>
module DefinerFilter =
    /// <summary>
    ///     Tries to remove symbols from the definitions in a
    ///     <c>FuncDefiner</c>.
    /// </summary>
    let tryRemoveFuncDefinerSymbols
      (defs : FuncDefiner<SVBoolExpr>)
      : Result<FuncDefiner<VBoolExpr>, TraversalError<Error>> =
        // TODO(CaptainHayashi): proper doc comment.
        // TODO(CaptainHayashi): stop assuming Definer is a list.
        defs
        |> List.map
               (fun (f, d) ->
                    let trav = removeSymFromBoolExpr UnwantedVarSym
                    let result = mapTraversal trav (normalBool d)
                    lift (mkPair f) result)
        |> collect

    /// <summary>
    ///     Filters a symbolic, indefinite definer into one containing only
    ///     non-symbolic views, which may be indefinite.
    /// </summary>
    let filterIndefiniteViewDefs
      (vds : FuncDefiner<SVBoolExpr option>)
      : Result<FuncDefiner<VBoolExpr option>, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        let partitionResult = partitionDefiner vds

        let assembleDefiniteDefiner indefs remdefs =
            let defseq = seq {
                for (v, d) in FuncDefiner.toSeq remdefs do yield (v, Some d)
                for (v, _) in FuncDefiner.toSeq indefs do yield (v, None) }
            FuncDefiner.ofSeq defseq

        let handlePartition (defs, indefs) =
            let removeResult = tryRemoveFuncDefinerSymbols defs
            let defResult = lift (assembleDefiniteDefiner indefs) removeResult
            // defResult has TraversalError errors, we need to lift them
            mapMessages Traversal defResult

        handlePartition partitionResult

    /// <summary>
    ///     Filters a symbolic, indefinite definer into one containing only
    ///     definite, non-symbolic views.
    /// </summary>
    let filterDefiniteViewDefs
      (vds : FuncDefiner<SVBoolExpr option>)
      : Result<FuncDefiner<VBoolExpr>, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        let partitionResult = partitionDefiner vds

        let handlePartition (defs, indefs) =
            // Complain if we have _any_ indefinite constraints.
            if List.isEmpty indefs
            then mapMessages Traversal (tryRemoveFuncDefinerSymbols defs)
            else
                let xs = Seq.toList (FuncDefiner.toSeq indefs)
                Bad (List.map (fst >> IndefiniteConstraint) xs)

        handlePartition partitionResult

    /// <summary>
    ///     Tries to convert a <c>ViewDef</C> based model into one over
    ///     non-symbolic constraints.
    /// </summary>
    /// <param name="model">
    ///     A model over <c>ViewDef</c>s.
    /// </param>
    /// <returns>
    ///     A <c>Result</c> over <c>Error</c> containing the
    ///     new model if the original contained only non-symbolic view
    ///     definitions.
    /// </returns>
    let filterModelNonSymbolicConstraints
      (model : Model<CmdTerm<SMBoolExpr, Reified<GView<Sym<MarkedVar>>>, SMVFunc>,
                     FuncDefiner<SVBoolExpr option>> )
      : Result<Model<CmdTerm<MBoolExpr, Reified<GView<MarkedVar>>, MVFunc>,
                     FuncDefiner<VBoolExpr option>>, Error> =
        let stripSymbolT =
            tliftOverCmdTerm
                (tliftOverExpr
                    (tliftOverCTyped (removeSymFromVar UnwantedMarkedVarSym)))

        let stripSymbols = mapTraversal stripSymbolT >> mapMessages Traversal
        let axiomFilterResult = tryMapAxioms stripSymbols model

        bind (tryMapViewDefs filterIndefiniteViewDefs) axiomFilterResult


/// <summary>
///     The instantiation phase.
///
///     <para>
///         This stage, which is used before predicate-based solvers
///         such as Z3, instantiates all views in the model, substituting
///         definitions for definite views and symbols for indefinite views.
///     </para>
/// </summary>
module Phase =
    /// Produces the predicate representation of an unguarded func.
    /// This corresponds to D^ in the theory.
    let interpretVFunc
      (definer : FuncDefiner<BoolExpr<Sym<Var>>>)
      (func : VFunc<Sym<MarkedVar>>)
      : Result<BoolExpr<Sym<MarkedVar>>, Error> =
        instantiate definer func
        |> lift (withDefault BTrue)  // Undefined views go to True by metatheory

    let interpretGFunc
      (definer : FuncDefiner<SVBoolExpr>)
      ({Cond = c; Item = i} : GFunc<Sym<MarkedVar>>)
      : Result<BoolExpr<Sym<MarkedVar>>, Error> =
        interpretVFunc definer i
        |> lift (mkImplies c)

    /// Interprets an entire view application over the given definer.
    let interpretGView
      (definer : FuncDefiner<SVBoolExpr>)
      (gview : GView<Sym<MarkedVar>>)
      : Result<BoolExpr<Sym<MarkedVar>>, Error> =
        let funcs = Multiset.toFlatSeq gview
        let interpretedFuncsR = collect (Seq.map (interpretGFunc definer) funcs)
        lift mkAnd interpretedFuncsR

    /// Given a symbolic-boolean term, calculate the non-symbolic approximation.
    let approxTerm (symterm : Term<SMBoolExpr, SMBoolExpr, SMBoolExpr>)
      : Result<Term<MBoolExpr, MBoolExpr, MBoolExpr>, Error> =
        (* This is needed to adapt approx's TraversalError<unit> into TraversalError<Error>.
           TODO(CaptainHayashi): It's horrible and I hate it, try fix somehow *)
        let toError =
            mapMessages
                (function
                 | Inner () -> failwith "toError: somehow approx returned Inner ()"
                 | BadType (x, y) -> BadType (x, y)
                 | ContextMismatch (x, y) -> ContextMismatch (x, y))

        let tryApproxInBool position boolExpr =
            (* First, try to replace symbols with Boolean approximates.
               This returns a pair of (useless) context and neq expression.
               Throw away the context with snd. *)
            let approxBoolExprR =
                lift snd (toError (tliftToBoolSrc approx position boolExpr))

            (* The above might have left some symbols, eg in integer position.
               Try to remove them, and fail if we can't. *)
            let elimBoolExprR =
                bind (normalBool >> mapTraversal (removeSymFromBoolExpr UnwantedMarkedVarSym))
                    approxBoolExprR
            // Finally, tidy up the resulting expression.
            mapMessages Traversal (lift simp elimBoolExprR)

        // Now work out how to approximate the individual bits of a Term.

        let mapCmd cmdSemantics =
            (* As well as general approximation, commands can be further
               approximated by removing certain part-symbolic parts of them.

               Commands appear on the LHS of a term, thus in -ve position. *)
            let removed = 
                Starling.Core.Command.SymRemove.removeSym cmdSemantics
            tryApproxInBool (Context.negative ()) (normalBool removed)

        // Weakest precondition is on the LHS of a term, thus in -ve position.
        let mapWPre wPre = tryApproxInBool (Context.negative ()) (normalBool wPre)
        // Goal is on the RHS of a term, thus in +ve position.
        let mapGoal goal = tryApproxInBool (Context.positive ()) (normalBool goal)

        tryMapTerm mapCmd mapWPre mapGoal symterm

    /// Interprets all of the views in a term over the given definer.
    let interpretTerm
      (definer : FuncDefiner<SVBoolExpr>)
      (approxMode : ApproxMode)
      (term : FinalTerm)
      : Result<SymProofTerm, Error> =
        let interpretedR =
            tryMapTerm
                (fun { CommandSemantics.Semantics = c } -> ok c)
                (fun g -> interpretGView definer g.Reified)
                (interpretVFunc definer)
                term

        let approxR =
            (* TODO(CaptainHayashi): check the errors to make sure we're not
               throwing away genuine failures. *)
            match approxMode with
            | NoApprox -> ok None
            | TryApprox -> ok (okOption (bind approxTerm interpretedR))
            | Approx -> lift Some (bind approxTerm interpretedR)

        lift2
            (fun interpreted approx ->
                { Original = term; SymBool = interpreted; Approx = approx })
            interpretedR
            approxR


    /// <summary>
    ///     Makes all indefinite viewdefs in a definer definite by defining them
    ///     as symbols.
    /// </summary>
    /// <param name="definer">
    ///     The view definer to convert.
    /// </param>
    /// <returns>
    ///     A <c>Definer</c> mapping each view func to a
    ///     <c>SVBoolExpr</c> giving its definition.  Indefinite
    ///     viewdefs are represented by symbols.
    /// </returns>
    let symboliseIndefinites
      (definer : FuncDefiner<SVBoolExpr option>)
      : Result<FuncDefiner<SVBoolExpr>, Error> =
        // First, work out which definitions are indefinite.
        let def, indef = partitionDefiner definer

        (* We now need to convert the definitions in 'indefSeq' such that they
           map the funcs to a symbol.  We do this by first making some helper
           functions. *)

        // Lifts variables in an expression into the Sym<> type with Reg.
        let exprToSym expr =
            mapTraversal
                (tliftToExprDest
                    (tliftOverCTyped (ignoreContext (Reg >> ok))))
                expr

        (* Constructs a definite view definition, given an indefinite view
           definition as a pair. *)
        let indefiniteFuncToSym ({ Name = n ; Params = ps }, _) =
            let convParamsR = collect (List.map exprToSym ps)

            let defR =
                lift (
                    fun convParams ->
                        BVar
                            (Sym 
                                (SymString (sprintf "!UNDEF:%A" n)
                                 :: List.map SymArg convParams)))
                    convParamsR

            lift (mkPair (func n ps)) defR

        // Now apply the above to all indefinites to create a new definer.
        let indefSeq = FuncDefiner.toSeq indef
        let indefSymSeqR = collect (Seq.map indefiniteFuncToSym indefSeq)
        let indefSymR = lift FuncDefiner.ofSeq indefSymSeqR

        // Merge the new definitions into our original definer.
        lift (FuncDefiner.combine def) (mapMessages Traversal indefSymR)


    /// <summary>
    ///     Run the instantiation phase.
    ///
    ///     <para>
    ///         This consumes the view definitions.
    ///     </para>
    /// </summary>
    /// <param name="approxMode">The approximation mode to use.</param>
    /// <param name="model">The model to instantiate.</param>
    /// <returns>
    ///     The model with all views instantiated.
    /// </returns>
    let run
      (approxMode : ApproxMode)
      (model : Model<CmdTerm<SMBoolExpr, Reified<GView<Sym<MarkedVar>>>, SMVFunc>,
                     FuncDefiner<SVBoolExpr option>>)
      : Result<Model<SymProofTerm, FuncDefiner<SVBoolExpr option>>, Error> =
      let vsR = symboliseIndefinites model.ViewDefs
      bind (fun vs -> tryMapAxioms (interpretTerm vs approxMode) model) vsR
