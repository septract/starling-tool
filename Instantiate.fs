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
open Starling.Core.Sub
open Starling.Core.Symbolic
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Sub


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
    let printError : Error -> Doc =
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

    let printSymProofTerm (sterm : SymProofTerm) : Doc =
        vsep
            [ headed "Original term" <|
                [ printCmdTerm
                    (printBoolExpr (printSym printMarkedVar))
                    (printGView (printSym printMarkedVar))
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
/// <typeparam name="dstVar">
///     The type of variables in the arguments being substituted.
/// </typeparam>
/// <returns>
///     A <c>VSubFun</c> performing the above substitutions.
/// </returns>
let paramSubFun
  ( { Params = fpars } : VFunc<'dstVar>)
  ( { Params = dpars } : DFunc)
  : VSubFun<Var, 'dstVar> =
    let pmap =
        Seq.map2 (fun par up -> valueOf par, up) dpars fpars
        |> Map.ofSeq

    Mapper.make
        (fun srcV ->
             match (pmap.TryFind srcV) with
             | Some (Typed.Int expr) -> expr
             | Some _ -> failwith "param substitution type error"
             | None -> failwith "free variable in substitution")
        (fun srcV ->
             match (pmap.TryFind srcV) with
             | Some (Typed.Bool expr) -> expr
             | Some _ -> failwith "param substitution type error"
             | None -> failwith "free variable in substitution")

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
    let subfun dfunc = paramSubFun vfunc dfunc |> liftVToSym |> onVars

    let checkedLookup =
        wrapMessages BadFuncLookup
            (flip FuncDefiner.lookupWithTypeCheck definer) vfunc

    lift
        (Option.map
            (fun (dfunc, defn) ->
                 defn |> Mapper.mapBoolCtx (subfun dfunc) NoCtx |> snd))
        checkedLookup
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
      : Result<FuncDefiner<VBoolExpr>, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        // TODO(CaptainHayashi): stop assuming Definer is a list.
        defs
        |> List.map
               (fun (f, d) ->
                    d
                    |> Mapper.mapBoolCtx (tsfRemoveSym UnwantedSym) NoCtx
                    |> snd
                    |> lift (mkPair f))
        |> collect

    /// <summary>
    ///     Filters a symbolic, indefinite definer into one containing only
    ///     non-symbolic views, which may be indefinite.
    /// </summary>
    let filterIndefiniteViewDefs
      (vds : FuncDefiner<SVBoolExpr option>)
      : Result<FuncDefiner<VBoolExpr option>, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        vds
        |> partitionDefiner
        |> function
           | (defs, indefs) ->
               defs
               |> tryRemoveFuncDefinerSymbols
               |> lift
                      (fun remdefs ->
                           FuncDefiner.ofSeq
                              (seq {
                                   for (v, d) in FuncDefiner.toSeq remdefs do
                                       yield (v, Some d)
                                   for (v, _) in FuncDefiner.toSeq indefs do
                                       yield (v, None)
                               } ))

    /// <summary>
    ///     Filters a symbolic, indefinite definer into one containing only
    ///     definite, non-symbolic views.
    /// </summary>
    let filterDefiniteViewDefs
      (vds : FuncDefiner<SVBoolExpr option>)
      : Result<FuncDefiner<VBoolExpr>, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        vds
        |> partitionDefiner
        |> function
           | defs, [] ->
               tryRemoveFuncDefinerSymbols defs
           | _, indefs ->
               indefs
               |> FuncDefiner.toSeq
               |> Seq.toList
               |> List.map (fst >> IndefiniteConstraint)
               |> Bad

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
        model
        |> tryMapAxioms (trySubExprInCmdTerm (tsfRemoveSym UnwantedSym) NoCtx >> snd)
        |> bind (tryMapViewDefs filterIndefiniteViewDefs)


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
        let tryApproxInBool position boolExpr =
            (* First, try to replace symbols with Boolean approximates.
               This returns a pair of (useless) context and neq expression. *)
            let _, approxBoolExpr =
                Mapper.mapBoolCtx
                    Starling.Core.Symbolic.Queries.approx
                    position
                    boolExpr
            (* The above might have left some symbols, eg in integer position.
               Try to remove them, and fail if we can't. *)
            let _, elimBoolExprR =
                Mapper.mapBoolCtx
                    (tsfRemoveSym UnwantedSym)
                    Sub.Types.SubCtx.NoCtx
                    approxBoolExpr
            // Finally, tidy up the resulting expression.
            lift simp elimBoolExprR

        let pos = Starling.Core.Sub.Position.positive
        let neg = Starling.Core.Sub.Position.negative

        // Now work out how to approximate the individual bits of a Term.

        let mapCmd cmdSemantics =
            (* As well as general approximation, commands can be further
               approximated by removing certain part-symbolic parts of them.

               Commands appear on the LHS of a term, thus in -ve position. *)
            tryApproxInBool neg
              (Starling.Core.Command.SymRemove.removeSym cmdSemantics)

        // Weakest precondition is on the LHS of a term, thus in -ve position.
        let mapWPre wPre = tryApproxInBool neg wPre
        // Goal is on the RHS of a term, thus in +ve position.
        let mapGoal goal = tryApproxInBool pos goal

        tryMapTerm mapCmd mapWPre mapGoal symterm

    /// Interprets all of the views in a term over the given definer.
    let interpretTerm
      (definer : FuncDefiner<SVBoolExpr>)
      (shouldApprox : bool)
      (term : FinalTerm)
      : Result<SymProofTerm, Error> =
        let interpretedR =
            tryMapTerm
                (fun { CommandSemantics.Semantics = c } -> ok c)
                (interpretGView definer)
                (interpretVFunc definer)
                term

        let approxR =
            if shouldApprox
            then lift Some (bind approxTerm interpretedR)
            else ok None

        lift2
            (fun interpreted approx ->
                { Original = term; SymBool = interpreted; Approx = approx })
            interpretedR
            approxR


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
      : FuncDefiner<SVBoolExpr> =
        let def, indef = partitionDefiner definer

        // Then, convert the indefs to symbols.
        let symconv = Mapper.make (Reg >> AVar) (Reg >> BVar)

        let idsym : FuncDefiner<SVBoolExpr> =
            indef
            |> FuncDefiner.toSeq
            |> Seq.map
                (fun ({ Name = n ; Params = ps }, _) ->
                    (func n ps,
                     BVar
                         (Sym
                              (func
                                   (sprintf "!UNDEF:%A" n)
                                   (List.map
                                       (Mapper.mapCtx symconv NoCtx >> snd)
                                       ps)))))
            |> FuncDefiner.ofSeq

        // TODO(CaptainHayashi): use functables properly.
        def @ idsym


    /// <summary>
    ///     Run the instantiation phase.
    ///
    ///     <para>
    ///         This consumes the view definitions.
    ///     </para>
    /// </summary>
    /// <param name="shouldApprox">Whether to build approximates.</param>
    /// <param name="model">The model to instantiate.</param>
    /// <returns>
    ///     The model with all views instantiated.
    /// </returns>
    let run
      (shouldApprox : bool)
      (model : Model<CmdTerm<SMBoolExpr, GView<Sym<MarkedVar>>, SMVFunc>,
                     FuncDefiner<SVBoolExpr option>>)
      : Result<Model<SymProofTerm, FuncDefiner<SVBoolExpr option>>, Error> =
      let vs = symboliseIndefinites model.ViewDefs
      tryMapAxioms (interpretTerm vs shouldApprox) model
