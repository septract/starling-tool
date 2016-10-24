/// <summary>
///     Func instantiation.
///
///     <para>
///         Starling has multiple stages during which we need to look up a
///         func in a list mapping funcs to Boolean expressions, and
///         substitute func's arguments for the parameters in that Boolean
///         expression.
///     </para>
///     <para>
///         This is the resposibility of <c>Starling.Core.Instantiate</c>,
///         which contains the function <c>instantiate</c> for this
///         purpose.
///      </para>
///     <para>
///         In addition, it contains more generic functions for looking
///         up funcs in tables, which are useful throughout Starling.
///     </para>
/// </summary>
module Starling.Core.Instantiate

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.TypeSystem.Check
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Model
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal


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
                GView<Sym<MarkedVar>>,
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
        | UnwantedSym of sym: string
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
        | UnwantedSym sym ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            fmt "encountered uninterpreted symbol {0}"
                [ String sym ]
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
                    (printGView (printSym printMarkedVar))
                    (printVFunc (printSym printMarkedVar))
                    sterm.Original ]
              headed "Symbolic conversion" <|
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
///     <c>_arg1</c> for their parameters in <c>_arg2</c>, over
///     symbolic variables.
///
///     <para>
///         The function takes a pair of hooks for transforming various
///         parts of the substitution function, because it is used
///         for generating <c>VSubFun</c>s for both <c>MarkedVar</c>s
///         and <c>Sym</c>s.
///     </para>
/// </summary>
/// <param name="_arg1">
///     The func providing the arguments to substitute.
/// </param>
/// <param name="_arg2">
///     The <c>DFunc</c> into which we are substituting.
/// </param>
/// <returns>
///     A <see cref="Traversal"/> performing the above substitutions.
/// </returns>
let paramSubFun
  (vfunc : VFunc<Sym<MarkedVar>>)
  ({ Params = dpars } : DFunc)
  : Traversal<TypedVar, Expr<Sym<MarkedVar>>, Error> =
    let fpars = vfunc.Params
    let pmap = Map.ofSeq (Seq.map2 (fun par up -> valueOf par, up) dpars fpars)

    ignoreContext
        (function
         | WithType (var, vtype) as v ->
            match pmap.TryFind var with
            | Some expr when vtype = typeOf expr -> ok expr
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
                lift Some (mapTraversal (subInBool dfunc) defn))
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
                    let trav = removeSymFromBoolExpr UnwantedSym
                    let result = mapTraversal trav d
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
    ///     definite or indefinite constraints.
    /// </summary>
    /// <param name="model">
    ///     A model over <c>ViewDef</c>s.
    /// </param>
    /// <returns>
    ///     A <c>Result</c> over <c>Error</c> containing the
    ///     new model if the original contained only definite view
    ///     definitions.
    /// </returns>
    let filterModelIndefinite
      (model : Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                     FuncDefiner<SVBoolExpr option>> )
      : Result<Model<CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>,
                     FuncDefiner<VBoolExpr option>>, Error> =
        let stripSymbolT =
            tliftOverCmdTerm
                (tliftOverExpr
                    (tliftOverCTyped (removeSymFromVar UnwantedSym)))

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
      : GView<Sym<MarkedVar>>
      -> Result<BoolExpr<Sym<MarkedVar>>, Error> =
        Multiset.toFlatSeq
        >> Seq.map (interpretGFunc definer)
        >> collect
        >> lift Seq.toList
        >> lift mkAnd

    /// Given a symbolic-boolean term, calculate the non-symbolic approximation.
    let approxTerm (symterm : Term<SMBoolExpr, SMBoolExpr, SMBoolExpr>)
      : Result<Term<MBoolExpr, MBoolExpr, MBoolExpr>, Error> =
        (* This is needed to adapt approx's TraversalError<unit> into TraversalError<Error>.
           It's horrible and I hate it. *)
        let toError =
            mapMessages
                (function
                 | Inner () -> failwith "toError: somehow approx returned Inner ()"
                 | BadType (x, y) -> BadType (x, y)
                 | ContextMismatch (x, y) -> ContextMismatch (x, y))

        let apr position =
            tliftToBoolSrc Starling.Core.Symbolic.Queries.approx
                position
            >> lift snd
            >> toError

        let sub = mapTraversal (removeSymFromBoolExpr UnwantedSym)

        let pos = Starling.Core.Traversal.Context.positive
        let neg = Starling.Core.Traversal.Context.negative

        let aprSubSimp position bool =
            let approxedResult = apr position bool
            let subbedResult = bind sub approxedResult
            let simpleResult = lift simp subbedResult
            mapMessages Traversal simpleResult

        let mapCmd cmdSemantics =
            let cmdSymRemoved =
                Starling.Core.Command.SymRemove.removeSym cmdSemantics
            aprSubSimp neg cmdSymRemoved

        tryMapTerm mapCmd (aprSubSimp neg) (aprSubSimp pos) symterm

    /// Interprets all of the views in a term over the given definer.
    let interpretTerm
      (definer : FuncDefiner<SVBoolExpr>)
      (approx : bool)
      (term : FinalTerm)
      : Result<SymProofTerm, Error> =
        let symboolResult =
            tryMapTerm
                (fun { CommandSemantics.Semantics = c } -> ok c)
                (interpretGView definer)
                (interpretVFunc definer)
                term

        // TODO(CaptainHayashi): don't do this unless the user requested it?
        let approxResult =
            if approx
            then lift Some (bind approxTerm symboolResult)
            else ok None

        lift2
            (fun s a ->
                { Original = term; SymBool = s; Approx = a })
            symboolResult
            approxResult


    /// <summary>
    ///     Converts all indefinite viewdefs to symbols.
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
        let def, indef = partitionDefiner definer

        // Then, convert the indefs to symbols.
        let symconv =
            mapTraversal
                (tliftToExprDest
                    (tliftOverCTyped (ignoreContext (Reg >> ok))))

        let indefSeq = FuncDefiner.toSeq indef

        let symbolise ({ Name = n ; Params = ps }, _) =
            let convParamsResult = collect (List.map symconv ps)

            let defResult =
                lift (func (sprintf "!UNDEF:%A" n) >> Sym >> BVar)
                    convParamsResult

            lift (mkPair (func n ps)) defResult

        let symbolisedResult = collect (Seq.map symbolise indefSeq)
        let idsymResult = lift FuncDefiner.ofSeq symbolisedResult

        // TODO(CaptainHayashi): use functables properly.
        lift (fun idsym -> def @ idsym) (mapMessages Traversal idsymResult)


    /// <summary>
    ///     Run the instantiation phase.
    ///
    ///     <para>
    ///         This consumes the view definitions.
    ///     </para>
    /// </summary>
    /// <param name="approx">Whether to build approximates.</param>
    /// <param name="model">The model to instantiate.</param>
    /// <returns>
    ///     The model with all views instantiated.
    /// </returns>
    let run
      (approx : bool)
      (model : Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                     FuncDefiner<SVBoolExpr option>>)
      : Result<Model<SymProofTerm, FuncDefiner<SVBoolExpr option>>, Error> =
        let vsResult = symboliseIndefinites model.ViewDefs
        bind (fun vs -> tryMapAxioms (interpretTerm vs approx) model) vsResult
