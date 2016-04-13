/// The part of the Z3 backend that translates terms to Z3.
module Starling.Backends.Z3

open Microsoft
open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Core.Instantiate
open Starling.Core.Sub
open Starling.Core.Z3
open Starling.Reifier
open Starling.Optimiser


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
        /// Produce a MuZ3 model; return `Response.MuTranslate`.
        | MuTranslate
        /// Produce a MuZ3 fixedpoint; return `Response.MuFix`.
        | MuFix
        /// Produce a MuZ3 sat list; return `Response.MuSat`.
        | MuSat

    /// <summary>
    ///     Type of MuZ3 results.
    /// </summary>
    type MuSat =
        /// <summary>
        ///     The proof succeeded with the <c>FuncDecl</c> being assigned
        ///     with the given <c>Expr</c>.
        /// </summary>
        | Sat of Z3.Expr
        /// <summary>
        ///     The proof failed with the assignments of the <c>FuncDecl</c>s
        ///     given by the <c>Expr</c>.
        /// </summary>
        | Unsat of Z3.Expr
        /// <summary>
        ///     The proof gave an odd result.
        /// </summary>
        | Unknown of reason: string

    /// <summary>
    ///     A MuZ3 model.
    /// </summary>
    type MuModel =
        { /// <summary>
          ///     List of definite viewdefs, as (view, def) pairs, to check.
          /// </summary>
          Definites : (VFunc * BoolExpr) list
          /// <summary>
          ///     Map of (view name, FuncDecl) bindings.
          /// </summary>
          FuncDecls : Map<string, Z3.FuncDecl>
          /// <summary>
          ///     List of fixedpoint rules.
          /// </summary>
          Rules : Map<string, Z3.BoolExpr> }

    /// Type of responses from the Z3 backend.
    [<NoComparison>]
    type Response =
        /// Output of the term translation step only.
        | Translate of Model<ZTerm, DFunc>
        /// Output of the final Z3 terms only.
        | Combine of Model<Z3.BoolExpr, DFunc>
        /// Output of satisfiability reports for the Z3 terms.
        | Sat of Map<string, Z3.Status>
        /// Output of the MuZ3 translation step only.
        | MuTranslate of MuModel
        /// Output of the MuZ3 fixedpoint generation step only.
        | MuFix of fixedpoint : Z3.Fixedpoint * unsafe : Z3.FuncDecl
        /// Output of the MuZ3 proof.
        | MuSat of MuSat

    /// A Z3 translation error.
    type Error =
        /// The translator was given an indefinite constraint.
        /// The Z3 backend cannot handle indefinite constraints.
        | IndefiniteConstraint of viewdef: DFunc
        /// Instantiation of a view failed.
        | InstantiationError of view: VFunc
                              * details: Starling.Core.Instantiate.Types.Error


/// <summary>
///     Pretty printers for the Z3 types.
/// </summary>
module Pretty =            
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Instantiate.Pretty
    open Starling.Core.Z3.Pretty

    /// Pretty-prints a MuSat.
    let printMuSat =
        function
        | MuSat.Sat ex -> vsep [ String "Proof FAILED."
                                 headed "Counter-example" [ printZ3Exp ex ] ]
        | MuSat.Unsat ex -> vsep [ String "Proof SUCCEEDED."
                                   headed "View assignments" [ printZ3Exp ex ] ]
        | MuSat.Unknown reason -> colonSep [ String "Proof status unknown"
                                             String reason ]
    
    /// Pretty-prints a MuModel.
    let printMuModel { Definites = ds ; Rules = rs ; FuncDecls = fdm } =
        printAssoc
            Indented
            [ (String "Definites",
               ds |>
               List.map (fun (f, d) -> equality (printVFunc f)
                                                (printBoolExpr d))
               |> vsep)
              (String "Rules",
               rs
               |> Map.toSeq
               |> Seq.map (fun (g, sym) ->
                               commaSep [ String (sym.ToString())
                                          String (g.ToString()) ] )
               |> vsep)
              (String "Goals",
               printMap Inline String (fun s -> String (s.ToString())) fdm) ]

    /// Pretty-prints a response.
    let printResponse mview =
        function
        | Response.Translate m ->
            printModelView
                mview
                (printTerm printZ3Exp printZ3Exp printZ3Exp)
                printDFunc
                m
        | Response.Combine m ->
            printModelView
                mview
                printZ3Exp
                printDFunc
                m
        | Response.Sat s ->
            printMap Inline String printSat s
        | Response.MuTranslate mm ->
            printMuModel mm
        | Response.MuFix (mf, _) ->
            String (mf.ToString ())
        | Response.MuSat s ->
            printMuSat s

    /// Pretty-prints Z3 translation errors.
    let printError =
        function
        | IndefiniteConstraint vd ->
            fmt "constraint of '{0}' is indefinite ('?'), and Z3 cannot use it"
                [ printDFunc vd ]
        | InstantiationError (vfunc, err) ->
            colonSep [ fmt "couldn't instantiate view '{0}'" [ printVFunc vfunc ]
                       printError err ]
    

/// <summary>
///     Functions for translating Starling elements into Z3.
/// </summary>
module Translator =
    open Starling.Core.Z3.Expr

    /// Produces the reification of an unguarded func.
    /// This corresponds to D^ in the theory.
    let interpretVFunc ft func =
        instantiate func ft
        |> lift (withDefault BTrue)  // Undefined views go to True by metatheory
        |> mapMessages (curry InstantiationError func)

    let interpretGFunc ft {Cond = c; Item = i} =
        interpretVFunc ft i
        |> lift (mkImplies c)

    /// Interprets an entire view application over the given functable.
    let interpretGView ft =
        Multiset.toFlatSeq
        >> Seq.map (interpretGFunc ft)
        >> collect
        >> lift Seq.toList
        >> lift mkAnd

    /// Interprets all of the views in a term over the given functable.
    let interpretTerm ft : STerm<GView, VFunc> -> Result<FTerm, Error> =
        tryMapTerm ok (interpretGView ft) (interpretVFunc ft)

    /// <summary>
    ///   Tries to make a <c>FuncTable</c> from <c>model</c>'s view definitions.
    /// </summary>
    /// <param name="model">
    ///   The model whose <c>ViewDefs</c> are to be turned into a <c>FuncTable</c>.
    /// </param>
    /// <returns>
    ///   A Chessie result, which, when ok, contains a <c>FuncTable</c> mapping
    ///   each defining view in <c>model</c> to its <c>BoolExpr</c> meaning.
    /// </returns>
    /// <remarks>
    ///   <para>
    ///     This stage requires all views in <c>model.ViewDefs</c> to be definite,
    ///     and will fail if any are not.
    ///   </para>
    /// </remarks>
    let makeFuncTable model =
        (* We cannot have any indefinite constraints for Z3.
           These are the snd in the pair coming from funcTableFromViewDefs. *)
        match (funcTableFromViewDefs model.ViewDefs) with
        | ftab, [] -> ok ftab
        | _, indefs -> indefs |> List.map IndefiniteConstraint |> Bad

    /// <summary>
    ///   Interprets all views in a model, converting them to <c>FTerm</c>s.
    /// </summary>
    /// <param name="model">
    ///   The model whose views are to be interpreted.
    /// </param>
    /// <returns>
    ///   A Chessie result, which, when ok, contains a <c>Model</c> equivalent to
    ///   <c>model</c> except that each view is replaced with the <c>BoolExpr</c>
    ///   interpretation of it from <c>model</c>'s <c>ViewDefs</c>.
    /// </returns>
    /// <remarks>
    ///   <para>
    ///     This stage requires all views in <c>model.ViewDefs</c> to be definite,
    ///     and will fail if any are not.
    ///   </para>
    /// </remarks>
    let interpret model : Result<Model<FTerm, DFunc>, Error> =
        makeFuncTable model
        |> bind (fun ft -> tryMapAxioms (interpretTerm ft) model)

    /// Combines the components of a reified term.
    let combineTerm (ctx: Z3.Context) {Cmd = c; WPre = w; Goal = g} =
        (* This is effectively asking Z3 to refute (c ^ w => g).
         *
         * This arranges to:
         *   - ¬(c^w => g) premise
         *   - ¬(¬(c^w) v g) def. =>
         *   - ((c^w) ^ ¬g) deMorgan
         *   - (c^w^¬g) associativity.
         *)
        boolToZ3 ctx (mkAnd [c ; w; mkNot g] )

    /// Combines reified terms into a list of Z3 terms.
    let combineTerms ctx = mapAxioms (combineTerm ctx)


/// <summary>
///     Functions for translating Starling elements into MuZ3.
/// </summary>
module MuTranslator =
    open Starling.Core.Z3.Expr

    /// <summary>
    ///     Converts a type into a Z3 sort.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use to generate the sorts.
    /// </param>
    /// <returns>
    ///     A function mapping types to sorts.
    /// </returns>
    let typeToSort (ctx : Z3.Context) =
        function
        | Type.Int -> ctx.MkIntSort () :> Z3.Sort
        | Type.Bool -> ctx.MkBoolSort () :> Z3.Sort

    (*
     * View definitions
     *)

    /// <summary>
    ///     Creates a <c>FuncDecl</c> from a <c>DFunc</c>.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context being used to create the <c>FuncDecl</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>DFunc</c> to model as a <c>FuncDecl</c>.
    /// </param>
    /// <returns>
    ///     A <c>FuncDecl</c> modelling the <c>DFunc</c>.
    /// </returns>
    let funcDeclOfDFunc (ctx : Z3.Context) { Name = n ; Params = pars } =
        ctx.MkFuncDecl(
            n,
            pars |> Seq.map (fst >> typeToSort ctx) |> Seq.toArray,
            ctx.MkBoolSort () :> Z3.Sort)

    /// <summary>
    ///     Creates an application of a <c>FuncDecl</c> to a list of
    ///     <c>Expr</c> parameters.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context being used to model the parameters.
    /// </param>
    /// <param name="funcDecl">
    ///     The <c>FuncDecl</c> to apply.
    /// </param>
    /// <param name="ps">
    ///     The <c>Expr</c> parameters to use.
    /// </param>
    /// <returns>
    ///     A <c>BoolExpr</c> representing an application of
    ///     <paramref name="ps"/> to <paramref name="funcDecl"/>.
    /// </returns>
    let applyFunc ctx (funcDecl : Z3.FuncDecl) ps =
        let psa : Z3.Expr[] = ps |> List.map (exprToZ3 ctx) |> List.toArray
        funcDecl.Apply psa
        :?> Z3.BoolExpr

    /// <summary>
    ///     Processes a view definition for MuZ3.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context being used to model the <c>ViewDef</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>ViewDef</c> to process.
    /// </param>
    /// <returns>
    ///     A pair of a pair of the name of the view and the <c>FuncDecl</c>
    ///     produced for the view, and an optional <c>BoolExpr</c>
    ///     assertion defining the view.
    /// </returns>
    let translateViewDef (ctx : Z3.Context) ( { View = vs; Def = ex } : ViewDef<DFunc> ) =
        let funcDecl = funcDeclOfDFunc ctx vs
        let mapEntry = (vs.Name, funcDecl)

        let rule =
            Option.map
                (fun dex ->
                     (* This is a definite constraint, so we want muZ3 to
                        use the existing constraint body for it.  We do this
                        by creating a rule that vs <=> dex.
                           
                        We need to make an application of our new FuncDecl to
                        create the constraints for it, if any.

                        The parameters of a DFunc are in (type, name) format,
                        which we need to convert to expression format first.
                        dex uses Unmarked constants, so we do too. *)
                     let eparams = List.map (uncurry (mkVarExp Unmarked)) vs.Params
                     let vfunc = { Name = vs.Name ; Params = eparams }

                     (vfunc, dex))
                ex

        (mapEntry, rule)

    /// <summary>
    ///     Constructs a declaration map and rule list from <c>ViewDef</c>s.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context being used to model the <c>ViewDef</c>s.
    /// </param>
    /// <param name="ds">
    ///     The sequence of <c>ViewDef</c>s to model.
    /// </param>
    /// <returns>
    ///     A tuple of a <c>Map</c> binding names to <c>FuncDecl</c>s and a
    ///     list of (view, def) pairs defining definite viewdefs.
    /// </returns>
    let translateViewDefs ctx ds =
        ds
        |> Seq.map (translateViewDef ctx)
        |> List.ofSeq
        |> List.unzip
        (* The LHS contains a list of tuples that need to make a map.
           The RHS needs to be filtered for indefinite constraints. *)
        |> pairMap Map.ofSeq (Seq.choose id)

    (*
     * Views
     *)

    /// <summary>
    ///     Models a <c>VFunc</c>.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use to model the func.
    /// </param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecls</c> to use in the modelling.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>VFunc</c> to model.
    /// </param>
    /// <returns>
    ///     A Z3 boolean expression relating to the <c>VFunc</c>.
    ///     If <paramref name="_arg1"/> is in <paramref name="funcDecls"/>, 
    ///     then the expression is an application of the <c>FuncDecl</c>
    ///     with the parameters in <paramref name="_arg1"/>.
    ///     Else, it is true.
    /// </returns>
    let translateVFunc ctx (funcDecls : Map<string, Z3.FuncDecl>) { Name = n ; Params = ps } =
        match funcDecls.TryFind n with
        | Some fd -> applyFunc ctx fd ps
        | None -> ctx.MkTrue ()

    /// <summary>
    ///     Models a <c>GView</c>.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use to model the func.
    /// </param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecls</c> to use in the modelling.
    /// </param>
    /// <returns>
    ///     A function taking a <c>GView</c> and returning a Z3
    ///     Boolean expression characterising it.
    /// </returns>
    let translateGView (ctx : Z3.Context) funcDecls =
        Multiset.toFlatSeq
        >> Seq.choose
               (fun { Cond = g ; Item = v } ->
                    let vZ = translateVFunc ctx funcDecls v
                    if (vZ.IsTrue)
                    then None
                    else Some <|
                         if (isTrue g)
                         then vZ
                         else (ctx.MkImplies (boolToZ3 ctx g, vZ)))
        >> Seq.toArray
        >> (fun a -> ctx.MkAnd a)

    (*
     * Variables
     *)

    /// <summary>
    ///     Constructs a rule implying view, whose body is a conjunction of
    ///     a <c>BoolExpr</c> and a <c>GView</c>.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use to model the func.
    /// </param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecls</c> to use in the modelling.
    /// </param>
    /// <param name="bodyExpr">
    ///     The body, as a Starling <c>BoolExpr</c>.  May be <c>BTrue</c> if
    ///     no view is desired.
    /// </param>
    /// <param name="bodyView">
    ///     The view part, as a Starling <c>GView</c>.  May be emp if no view
    ///     is desired.
    /// </param>
    /// <param name="head">
    ///     The <c>VFunc</c> making up the head.
    /// </param>
    /// <returns>
    ///     An <c>Option</c>al rule, which is present only if <c>head</c> is defined
    ///     in <c>funcDecls</c>.
    ///
    ///     If present, the rule is of the form <c>(forall (vars) (=> body
    ///     func))</c>, where <c>vars</c> is the union of the variables in
    ///     <c>body</c>, <c>gview</c> and <c>head</c>.
    /// </returns>
    let mkRule (ctx : Z3.Context) funcDecls bodyExpr bodyView head =
        let vars =
            seq {
                yield! (varsInBool bodyExpr)

                for gfunc in Multiset.toFlatList bodyView do
                    yield! (varsInGFunc gfunc)

                yield! (varsInVFunc head)
            }
            // Make sure we don't quantify over a variable twice.
            |> Set.ofSeq
            |> Set.map (fun (name, ty) ->
                            ctx.MkConst (constToString name, typeToSort ctx ty))
            |> Set.toArray

        let bodyExprZ = boolToZ3 ctx bodyExpr

        let bodyZ =
            if (Multiset.length bodyView = 0)
            then bodyExprZ
            else ctx.MkAnd [| bodyExprZ ; translateGView ctx funcDecls bodyView |]

        let headZ = translateVFunc ctx funcDecls head
        if headZ.IsTrue
        then None
        else Some (ctx.MkForall (vars, ctx.MkImplies (bodyZ, headZ))
                   :> Z3.BoolExpr)

    /// <summary>
    ///     Constructs a rule for initialising a variable.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use to model the rule.
    /// </param>
    /// <param name="funcs">
    ///     A map of active view <c>FuncDecl</c>s.
    /// </param>
    /// <param name="svars">
    ///     Map of shared variables in the program.
    /// </param>
    /// <returns>
    ///     A sequence containing at most one pair of <c>string</c> and
    ///     Z3 <c>BoolExpr</c> representing the variable initialisation rule.
    /// </returns>
    let translateVariables ctx funcDecls svars =
        let vpars =
            svars
            |> Map.toList
            |> List.map (uncurry (flip (mkVarExp Unmarked)))

        // TODO(CaptainHayashi): actually get these initialisations from
        // somewhere.
        let body =
            vpars
            |> List.map
                   (fun v -> BEq (v,
                                  match v with
                                  | AExpr _ -> AExpr (AInt 0L)
                                  | BExpr _ -> BExpr (BFalse)))
            |> mkAnd

        let head = { Name = "emp" ; Params = vpars }

        mkRule ctx funcDecls body Multiset.empty head
        |> function
           | Some x -> Seq.singleton ("init", x)
           | None -> Seq.empty


    (*
     * Terms
     *)

    /// <summary>
    ///     Constructs a muZ3 rule for a proof term.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use for modelling the term.
    /// </param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecl</c>s to use when creating view
    ///     applications.
    /// </param>
    /// <param name="_arg1">
    ///     Pair of term name and <c>Term</c>.
    /// </param>
    /// <returns>
    ///     An <c>Option</c> containing a pair of the term name and the Z3
    ///     <c>BoolExpr</c> representing the rule form of the proof term.
    /// </returns>
    let translateTerm ctx funcDecls (name : string, {Cmd = c ; WPre = w ; Goal = g}) =
        mkRule ctx funcDecls c w g |> Option.map (mkPair name)

    /// <summary>
    ///     Constructs muZ3 rules and goals for a model.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use for modelling the fixpoint.
    /// </param>
    /// <param name="_arg1">
    ///     The model to turn into a fixpoint.
    /// </param>
    /// <returns>
    ///     A pair of the sequence of (<c>BoolExpr</c>, <c>Symbol</c>) goals
    ///     used to prove the model, and the map of names to <c>FuncDecl</c>s
    ///     to use to start queries.
    /// </returns>
    let translate ctx { Globals = svars ; ViewDefs = ds ; Axioms = xs } =
        let funcDecls, definites = translateViewDefs ctx ds
        let vrules = translateVariables ctx funcDecls svars
        let trules = xs |> Map.toSeq |> Seq.choose (translateTerm ctx funcDecls)

        { Definites = List.ofSeq definites
          Rules = Seq.append vrules trules |> Map.ofSeq
          FuncDecls = funcDecls }

    /// <summary>
    ///     Generates a MuZ3 fixedpoint.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use for modelling the fixedpoint.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>MuModel</c> to use in generation.
    /// </param>
    /// <returns>
    ///     The pair of Z3 <c>Fixedpoint</c> and unsafeness <c>FuncDecl</c>.
    /// </returns>
    let fixgen (ctx : Z3.Context) { Definites = ds; Rules = rs ; FuncDecls = fm } =
        let fixedpoint = ctx.MkFixedpoint ()

        let pars = ctx.MkParams ()
        pars.Add("engine", ctx.MkSymbol("pdr"))
        fixedpoint.Parameters <- pars

        List.iter
            (fun (view, def) ->
                 match (mkRule ctx fm def Multiset.empty view) with
                 | Some rule -> fixedpoint.AddRule rule
                 | None -> ())
            ds

        let unsafe = ctx.MkFuncDecl ("unsafe", [||], ctx.MkBoolSort () :> Z3.Sort)
        fixedpoint.RegisterRelation unsafe
        let unsafeapp = unsafe.Apply [| |] :?> Z3.BoolExpr

        List.iter
            (fun (view, def) ->
                 // TODO(CaptainHayashi): de-duplicate this with mkRule.
                 let vars =
                    seq {
                        yield! (varsInBool def)
                        for param in view.Params do
                            yield! (varsIn param)
                    }
                    |> Set.ofSeq
                    |> Set.map (fun (name, ty) ->
                                    ctx.MkConst (constToString name, typeToSort ctx ty))
                    |> Set.toArray

                 fixedpoint.AddRule (
                    ctx.MkForall (vars,
                                  ctx.MkImplies (ctx.MkAnd [| def |> mkNot |> boolToZ3 ctx
                                                              translateVFunc ctx fm view |],
                                                 unsafeapp))))
            ds

        Map.iter (fun (s : string) g -> fixedpoint.AddRule (g, ctx.MkSymbol s :> Z3.Symbol)) rs
        Map.iter (fun _ g -> fixedpoint.RegisterRelation g) fm

        (fixedpoint, unsafe)

    /// <summary>
    ///     Runs a MuZ3 fixedpoint.
    /// </summary>
    /// <param name="fixedpoint">
    ///     The <c>Fixedpoint</c> to run.
    /// </param>
    /// <param name="unsafe">
    ///     The <c>FuncDecl</c> naming the unsafeness predicate.
    /// </param>
    /// <returns>
    ///     A <c>MuResult</c>.
    /// </returns>
    let run (fixedpoint : Z3.Fixedpoint) unsafe =
        match (fixedpoint.Query [| unsafe |]) with
        | Z3.Status.SATISFIABLE ->
             MuSat.Sat (fixedpoint.GetAnswer ())
        | Z3.Status.UNSATISFIABLE ->
             MuSat.Unsat (fixedpoint.GetAnswer ())
        | Z3.Status.UNKNOWN ->
             MuSat.Unknown (fixedpoint.GetReasonUnknown ())
         | _ -> MuSat.Unknown "query result out of bounds"


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


/// Shorthand for the translator stage of the MuZ3 pipeline.
let mutranslate = MuTranslator.translate
/// Shorthand for the fixpoint generation stage of the MuZ3 pipeline.
let mufix = MuTranslator.fixgen
/// Shorthand for the satisfiability stage of the MuZ3 pipeline.
let musat = uncurry MuTranslator.run
/// Shorthand for the translator stage of the Z3 pipeline.
let translate = Translator.interpret
/// Shorthand for the combination stage of the Z3 pipeline.
let combine = Translator.combineTerms >> lift
/// Shorthand for the satisfiability stage of the Z3 pipeline.
let sat = Run.run >> lift

/// Runs the Starling Z3 backend.
/// Takes two arguments: the first is the `Response` telling the backend what
/// to output; the second is the reified model to process with Z3.
let run resp =
    use ctx = new Z3.Context()
    match resp with
    | Request.Translate ->
        translate
        >> lift (mapAxioms (mapTerm (Expr.boolToZ3 ctx)
                                    (Expr.boolToZ3 ctx)
                                    (Expr.boolToZ3 ctx)))
        >> lift Response.Translate
    | Request.Combine -> translate >> combine ctx >> lift Response.Combine
    | Request.Sat -> translate >> combine ctx >> sat ctx >> lift Response.Sat
    | Request.MuTranslate ->
        mutranslate ctx
        >> Response.MuTranslate
        >> ok
    | Request.MuFix ->
        mutranslate ctx
        >> mufix ctx
        >> Response.MuFix
        >> ok
    | Request.MuSat ->
        mutranslate ctx
        >> mufix ctx
        >> musat
        >> Response.MuSat
        >> ok
