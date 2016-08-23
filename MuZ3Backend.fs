/// <summary>
///     The MuZ3 backend.
///
///     <para>
///         Like the Z3 backend, this uses Z3 as a solver.  Unlike the
///         Z3 backend, we use the experimental MuZ3 fixedpoint solver
///         framework instead of using Z3 as an SMT solver.
///     </para>
///     <para>
///         Similarly to the HSF backend, this converts Starling proof
///         terms into (command && w/pre => goal) clauses, where each
///         view is left uninterpreted.  Unlike the HSF backend, we
///         build an 'unsafe' predicate, which is true when we detect
///         that a definite view expression has been weakened from its
///         definition.  We also ensure that view definitions cannot be
///         strengthened by asserting them as rules.
///     </para>
///     <para>
///         MuZ3 can handle indefinite constraints and unknown views,
///         and does not require external programs.  However, it is
///         slow and very experimental, both in terms of the external
///         solver and our support for it.
///     </para>
/// </summary>

module Starling.Backends.MuZ3

open Microsoft
open Starling
open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.View.Sub
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Sub
open Starling.Core.Instantiate
open Starling.Core.Sub
open Starling.Core.Z3
open Starling.Reifier
open Starling.Optimiser


/// <summary>
///     Types for the MuZ3 backend.
/// </summary>
[<AutoOpen>]
module Types =
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
          Definites : (VFunc<Var> * BoolExpr<Var>) list
          /// <summary>
          ///     Map of (view name, FuncDecl) bindings.
          /// </summary>
          FuncDecls : Map<string, Z3.FuncDecl>
          /// <summary>
          ///     List of fixedpoint rules.
          /// </summary>
          Rules : Map<string, Z3.BoolExpr> }

    /// <summary>
    ///     Type of requests to the MuZ3 backend.
    /// </summary>
    type Request =
        /// Produce a MuZ3 model; return `Response.MuTranslate`.
        | Translate
        /// Produce a MuZ3 fixedpoint; return `Response.MuFix`.
        | Fix
        /// Produce a MuZ3 sat list; return `Response.MuSat`.
        | Sat

    /// <summary>
    ///     Type of responses from the MuZ3 backend.
    /// </summary>
    [<NoComparison>]
    type Response =
        /// Output of the MuZ3 translation step only.
        | Translate of MuModel
        /// Output of the MuZ3 fixedpoint generation step only.
        | Fix of fixedpoint : Z3.Fixedpoint * unsafe : Z3.FuncDecl
        /// Output of the MuZ3 proof.
        | Sat of MuSat


/// <summary>
///     Pretty printers for the MuZ3 types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty
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
               List.map (fun (f, d) -> equality (printVFunc String f)
                                                (printVBoolExpr d))
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
        | Response.Translate mm ->
            printMuModel mm
        | Response.Fix (mf, _) ->
            String (mf.ToString ())
        | Response.Sat s ->
            printMuSat s


/// <summary>
///     Functions for translating Starling elements into MuZ3.
/// </summary>
module Translator =
    open Starling.Core.Z3.Expr

    /// <summary>
    ///     Converts a type into a Z3 sort.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context to use to generate the sorts.
    /// </param>
    /// <returns>
    ///     A function mapping types to sorts.
    /// </returns>
    let typeToSort reals (ctx : Z3.Context) =
        function
        | Type.Int _ when reals -> ctx.MkRealSort () :> Z3.Sort
        | Type.Int _ -> ctx.MkIntSort () :> Z3.Sort
        | Type.Bool _ -> ctx.MkBoolSort () :> Z3.Sort

    (*
     * View definitions
     *)

    /// <summary>
    ///     Creates a <c>FuncDecl</c> from a <c>DFunc</c>.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context being used to create the <c>FuncDecl</c>.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>DFunc</c> to model as a <c>FuncDecl</c>.
    /// </param>
    /// <returns>
    ///     A <c>FuncDecl</c> modelling the <c>DFunc</c>.
    /// </returns>
    let funcDeclOfDFunc reals (ctx : Z3.Context) { Name = n ; Params = pars } =
        ctx.MkFuncDecl(
            n,
            pars |> Seq.map (typeOf >> typeToSort reals ctx) |> Seq.toArray,
            ctx.MkBoolSort () :> Z3.Sort)

    /// <summary>
    ///     Creates an application of a <c>FuncDecl</c> to a list of
    ///     <c>Expr</c> parameters.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context being used to model the parameters.
    /// </param>
    /// <param name="funcDecl">
    ///     The <c>FuncDecl</c> to apply.
    /// </param>
    /// <param name="ps">
    ///     The <c>Expr</c> parameters to use.
    /// </param>
    /// <typeparam name="var">
    ///     The meta-type of variables in the parameters.
    /// </typeparam>
    /// <returns>
    ///     A <c>BoolExpr</c> representing an application of
    ///     <paramref name="ps"/> to <paramref name="funcDecl"/>.
    /// </returns>
    let applyFunc
      (reals : bool)
      (toVar : 'var -> Var)
      (ctx : Z3.Context)
      (funcDecl : Z3.FuncDecl)
      (ps : Expr<'var> list)
      : Z3.BoolExpr =
        let psa : Z3.Expr[] =
            ps |> List.map (exprToZ3 reals toVar ctx) |> List.toArray

        funcDecl.Apply psa :?> Z3.BoolExpr

    /// <summary>
    ///     Processes a view definition for MuZ3.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
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
    let translateViewDef
      (reals : bool)
      (ctx : Z3.Context)
      (vs : DFunc, ex)
      : ((string * Z3.FuncDecl) * ((VFunc<Var> * VBoolExpr) option))=
        let funcDecl = funcDeclOfDFunc reals ctx vs
        let mapEntry = (vs.Name, funcDecl)

        let rule =
            Option.map
                (fun dex ->
                     (* This is a definite constraint, so we want muZ3 to
                        use the existing constraint body for it.  We do this
                        by creating a rule that vs <=> dex.

                        We need to make an application of our new FuncDecl to
                        create the constraints for it, if any.

                        The parameters of a DFunc are in parameter format,
                        which we need to convert to expression format first.
                        dex uses Unmarked constants, so we do too. *)
                     let eparams = List.map (mkVarExp id) vs.Params
                     let vfunc = { Name = vs.Name ; Params = eparams }

                     (vfunc, dex))
                ex

        (mapEntry, rule)

    /// <summary>
    ///     Constructs a declaration map and rule list from <c>ViewDef</c>s.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
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
    let translateViewDefs
      (reals : bool)
      (ctx : Z3.Context)
      (ds : FuncDefiner<BoolExpr<Var> option>)
      : (Map<string, Z3.FuncDecl>
         * (VFunc<Var> * BoolExpr<Var>) seq) =
        ds
        |> Seq.map (translateViewDef reals ctx)
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
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="toVar">
    ///     A function converting variables in the <c>BoolExpr</c> into
    ///     <c>Var</c>s: for example, <c>constToString</c>.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context to use to model the func.
    /// </param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecls</c> to use in the modelling.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>VFunc</c> to model.
    /// </param>
    /// <typeparam name="var">
    ///     The meta-type of variables in the <c>VFunc</c>.
    /// </typeparam>
    /// <returns>
    ///     A Z3 boolean expression relating to the <c>VFunc</c>.
    ///     If <paramref name="_arg1"/> is in <paramref name="funcDecls"/>,
    ///     then the expression is an application of the <c>FuncDecl</c>
    ///     with the parameters in <paramref name="_arg1"/>.
    ///     Else, it is true.
    /// </returns>
    let translateVFunc
      (reals : bool)
      (toVar : 'var -> Var)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      ( { Name = n ; Params = ps } : VFunc<'var>)
      : Z3.BoolExpr =
        match funcDecls.TryFind n with
        | Some fd -> applyFunc reals toVar ctx fd ps
        | None -> ctx.MkTrue ()

    /// <summary>
    ///     Models a <c>GView</c>.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="toVar">
    ///     A function converting variables in the <c>BoolExpr</c> into
    ///     <c>Var</c>s: for example, <c>constToString</c>.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context to use to model the func.
    /// </param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecls</c> to use in the modelling.
    /// </param>
    /// <typeparam name="var">
    ///     The meta-type of variables in the <c>GView</c>.
    /// </typeparam>
    /// <returns>
    ///     A function taking a <c>GView</c> and returning a Z3
    ///     Boolean expression characterising it.
    /// </returns>
    let translateGView
      (reals : bool)
      (toVar : 'var -> Var)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      : GView<'var> -> Z3.BoolExpr =
        Multiset.toFlatSeq
        >> Seq.choose
               (fun { Cond = g ; Item = v } ->
                    let vZ = translateVFunc reals toVar ctx funcDecls v
                    if (vZ.IsTrue)
                    then None
                    else Some <|
                         if (isTrue g)
                         then vZ
                         else (ctx.MkImplies (boolToZ3 reals toVar ctx g, vZ)))
        >> Seq.toArray
        >> (fun a -> ctx.MkAnd a)

    (*
     * Rule building
     *)

    /// <summary>
    ///     Makes an optimised implication between two Z3 expressions,
    ///     universally quantified over a set of variables.
    /// </summary>
    /// <param name="ctx">
    ///     The Z3 context to use to model the entailment.
    /// </param>
    /// <param name="vars">
    ///     An array of Z3 <c>Expr</c>s representing variables to be
    ///     quantified.  If this is empty, no quantification is done.
    /// </param>
    /// <param name="head">
    ///     The Z3 <c>BoolExpr</c> to be implied.  If this is a
    ///     tautology, the entire implication is thrown away.
    /// </param>
    /// <param name="body">
    ///     The Z3 <c>BoolExpr</c> on the LHS of the implication.
    ///     If this is a tautology, the head is substituted for the
    ///     implication.  If it is a contradiction, the entire
    ///     implication is thrown away.
    /// </param>
    /// <returns>
    ///     A Z3 expression implementing the quantified implication.
    /// </returns>
    let mkQuantifiedEntailment (ctx : Z3.Context)
                               vars
                               (body : Z3.BoolExpr)
                               (head : Z3.BoolExpr) =
        (* Don't emit if the head is true: not only is the result true,
           trivial, but MuZ3 will complain about interpreted heads later.
           Also don't emit if the body is false: these are also always true. *)
        if head.IsTrue || body.IsFalse
        then None
        else
            let core =
                if body.IsTrue
                then head
                else if head.IsFalse
                then ctx.MkNot body
                else ctx.MkImplies (body, head)

            (* If this rule involves one or more variables, we must universally
               quantify over them.
               MuZ3 will complain if we universally quantify over nothing,
               though, so we need to be careful! *)
            Some (if Array.isEmpty vars
                  then core
                  else ctx.MkForall (vars, core) :> Z3.BoolExpr)

    /// <summary>
    ///     Constructs a rule implying a view, whose body is a conjunction of
    ///     a <c>BoolExpr</c> and a <c>GView</c>.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="toVar">
    ///     A function converting variables in the <c>BoolExpr</c> into
    ///     <c>Var</c>s: for example, <c>constToString</c>.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context to use to model the rule.
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
    /// <typeparam name="var">
    ///     The meta-type of variables in the body of the rule.
    /// </typeparam>
    /// <returns>
    ///     An <c>Option</c>al rule, which is present only if <c>head</c> is defined
    ///     in <c>funcDecls</c>.
    ///
    ///     If present, the rule is of the form <c>(forall (vars) (=> body
    ///     func))</c>, where <c>vars</c> is the union of the variables in
    ///     <c>body</c>, <c>gview</c> and <c>head</c>.
    /// </returns>
    let mkRule
      (reals : bool)
      (toVar : 'var -> Var)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (bodyExpr : BoolExpr<'var>)
      (bodyView : GView<'var>)
      (head : VFunc<'var>)
      : Z3.BoolExpr option =
        let vsub = (liftCToSub (Mapper.cmake toVar))

        // First, make everything use string variables.
        let _, bodyExpr' = Mapper.mapBoolCtx vsub NoCtx bodyExpr
        let _, bodyView' = subExprInGView vsub NoCtx bodyView
        let _, head' = subExprInVFunc vsub NoCtx head

        let vars =
            seq {
                yield! (mapOverVars Mapper.mapBoolCtx findVars bodyExpr')

                for gfunc in Multiset.toFlatList bodyView' do
                    yield! (mapOverVars Sub.subExprInGFunc findVars gfunc)

                yield! (mapOverVars Sub.subExprInVFunc findVars head')
            }
            // Make sure we don't quantify over a variable twice.
            |> Set.ofSeq
            |> Set.map (fun p ->
                            ctx.MkConst (p |> valueOf,
                                         p |> typeOf |> typeToSort reals ctx))
            |> Set.toArray

        let bodyExprZ = boolToZ3 reals id ctx bodyExpr'

        let bodyZ =
            if (Multiset.length bodyView = 0)
            then bodyExprZ
            else
                ctx.MkAnd
                    [| bodyExprZ
                       translateGView reals id ctx funcDecls bodyView' |]

        let headZ = translateVFunc reals id ctx funcDecls head'

        mkQuantifiedEntailment ctx vars bodyZ headZ


    (*
     * Variables
     *)

    /// <summary>
    ///     Constructs a rule for initialising a variable.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
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
    let translateVariables reals ctx funcDecls svars =
        let vpars =
            svars
            |> Map.toList
            |> List.map (fun (v, t) -> mkVarExp id (withType t v))

        // TODO(CaptainHayashi): actually get these initialisations from
        // somewhere.
        let body =
            vpars
            |> List.map
                   (fun v -> BEq (v,
                                  match v with
                                  | Expr.Int _ -> Expr.Int (AInt 0L)
                                  | Expr.Bool _ -> Expr.Bool (BFalse)))
            |> mkAnd

        let head = { Name = "emp" ; Params = vpars }

        mkRule reals id ctx funcDecls body Multiset.empty head
        |> function
           | Some x -> Seq.singleton ("init", x)
           | None -> Seq.empty


    (*
     * Terms
     *)

    /// <summary>
    ///     Constructs a muZ3 rule for a proof term.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
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
    let translateTerm reals ctx funcDecls (name : string, {Cmd = c ; WPre = w ; Goal = g}) =
        mkRule reals unmarkVar ctx funcDecls c w g |> Option.map (mkPair name)

    /// <summary>
    ///     Constructs muZ3 rules and goals for a model.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
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
    let translate
      reals
      (ctx : Z3.Context)
      ({ Globals = svars ; ViewDefs = ds ; Axioms = xs }
         : Model<Term<MBoolExpr, GView<MarkedVar>, MVFunc>,
                 FuncDefiner<BoolExpr<Var> option>> ) =
        let funcDecls, definites = translateViewDefs reals ctx ds
        let vrules = translateVariables reals ctx funcDecls svars
        let trules = xs |> Map.toSeq |> Seq.choose (translateTerm reals ctx funcDecls)

        { Definites = List.ofSeq definites
          Rules = Seq.append vrules trules |> Map.ofSeq
          FuncDecls = funcDecls }


/// <summary>
///     Proof execution using MuZ3.
/// </summary>
module Run =
    open Starling.Core.Z3.Expr

    /// <summary>
    ///     Generates a MuZ3 fixedpoint.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context to use for modelling the fixedpoint.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>MuModel</c> to use in generation.
    /// </param>
    /// <returns>
    ///     The pair of Z3 <c>Fixedpoint</c> and unsafeness <c>FuncDecl</c>.
    /// </returns>
    let fixgen reals (ctx : Z3.Context) { Definites = ds; Rules = rs ; FuncDecls = fm } =
        let fixedpoint = ctx.MkFixedpoint ()

        let pars = ctx.MkParams ()
        pars.Add("engine", ctx.MkSymbol("pdr"))
        fixedpoint.Parameters <- pars

        List.iter
            (fun (view, def) ->
                 match (Translator.mkRule reals id ctx fm def Multiset.empty view) with
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
                         yield! (mapOverVars Mapper.mapBoolCtx findVars def)
                         for param in view.Params do
                             yield! (mapOverVars Mapper.mapCtx findVars param)
                     }
                     |> Set.ofSeq
                     |> Set.map
                            (fun (var : CTyped<Var>) ->
                                 ctx.MkConst (valueOf var,
                                              Translator.typeToSort reals ctx (typeOf var)))
                     |> Set.toArray

                 // Introduce 'V ^ ¬D(V) -> unsafe'.
                 Translator.mkQuantifiedEntailment
                     ctx
                     vars
                     (ctx.MkAnd [| def |> mkNot |> boolToZ3 reals id ctx
                                   Translator.translateVFunc reals id ctx fm view |])
                     unsafeapp
                 |> Option.iter (fixedpoint.AddRule))
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


/// Shorthand for the translator stage of the MuZ3 pipeline.
let translate = Translator.translate
/// Shorthand for the fixpoint generation stage of the MuZ3 pipeline.
let fix = Run.fixgen
/// Shorthand for the satisfiability stage of the MuZ3 pipeline.
let sat = uncurry Run.run

/// <summary>
///     The Starling MuZ3 backend driver.
/// </summary>
/// <param name="reals">
///     Whether to use Real instead of Int.
///     This can be faster, but is slightly inaccurate.
/// </param>
/// <param name="req">
///     The request to handle.
/// </param>
/// <returns>
///     A function implementing the chosen MuZ3 backend process.
/// </returns>
let run reals req =
    use ctx = new Z3.Context()
    match req with
    | Request.Translate ->
        translate reals ctx
        >> Response.Translate
    | Request.Fix ->
        translate reals ctx
        >> fix reals ctx
        >> Response.Fix
    | Request.Sat ->
        translate reals ctx
        >> fix reals ctx
        >> sat
        >> Response.Sat
