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

open Chessie.ErrorHandling
open Microsoft
open Starling
open Starling.Collections
open Starling.Semantics
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Traversal
open Starling.Core.Instantiate
open Starling.Core.Traversal
open Starling.Core.Symbolic
open Starling.Core.Z3
open Starling.Reifier
open Starling.Optimiser


/// <summary>
///     Types for the MuZ3 backend.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     An error caused when emitting a Horn clause.
    /// </summary>
    type Error =
        /// <summary>
        ///     MuZ3 can't check the given deferred check.
        /// </summary>
        | CannotCheckDeferred of check : DeferredCheck * why : string
        /// <summary>
        ///     One of our traversals bought the farm.
        /// </summary>
        | Traversal of err : TraversalError<Error>
        /// <summary>
        ///     Arrays were encountered: these are not yet supported.
        /// </summary>
        | ArraysNotSupported

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
    open Starling.Core.Traversal.Pretty
    open Starling.Core.Z3.Pretty

    /// <summary>
    ///     Pretty-prints a MuZ3 backend error.
    /// </summary>
    /// <param name="err">The error to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="err"/>.
    /// </returns>
    let rec printError (err : Error) : Doc =
        match err with
        | CannotCheckDeferred (check, why) ->
            (errorStr "deferred sanity check"
             <+> quoted (printDeferredCheck check)
             <+> errorStr "failed:"
             <+> String why)
        | Traversal err -> printTraversalError printError err
        | ArraysNotSupported ->
            errorStr "arrays are not yet supported in muZ3"

    /// Pretty-prints a MuSat.
    let printMuSat : MuSat -> Doc =
        function
        | MuSat.Sat ex -> vsep [ String "Proof FAILED."
                                 headed "Counter-example" [ printZ3Exp ex ] ]
        | MuSat.Unsat ex -> vsep [ String "Proof SUCCEEDED."
                                   headed "View assignments" [ printZ3Exp ex ] ]
        | MuSat.Unknown reason -> colonSep [ String "Proof status unknown"
                                             String reason ]

    /// Pretty-prints a MuModel.
    let printMuModel
      ({ Definites = ds ; Rules = rs ; FuncDecls = fdm } : MuModel)
      : Doc =
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
    let printResponse (mview : ModelView) : Response -> Doc =
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
    let funcDeclOfDFunc
      (reals : bool)
      (ctx : Z3.Context)
      ({ Name = n ; Params = pars } : DFunc)
      : Z3.FuncDecl =
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
                     let eparams = List.map mkVarExp vs.Params
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
                   // Guards are always 'bool'
                   let gT = mkTypedSub normalRec g

                   let vZ = translateVFunc reals toVar ctx funcDecls v
                   if (vZ.IsTrue)
                   then None
                   else
                        Some
                            (if (isTrue g)
                             then vZ
                             else (ctx.MkImplies (boolToZ3 reals toVar ctx gT, vZ))))
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
    ///     An optional Z3 expression implementing the quantified implication.
    /// </returns>
    let mkQuantifiedEntailment
      (ctx : Z3.Context)
      (vars : Z3.Expr[])
      (body : Z3.BoolExpr)
      (head : Z3.BoolExpr)
      : Z3.BoolExpr option =
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
    /// <param name="ctx">The Z3 context to use to model the rule.</param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecls</c> to use in the modelling.
    /// </param>
    /// <param name="bodyExpr">
    ///     The body, as a Starling <c>BoolExpr</c>.  May be <c>BTrue</c> if
    ///     no non-view body expression is desired.
    /// </param>
    /// <param name="bodyView">
    ///     The view part, as a Starling <c>GView</c>.  May be emp if no view
    ///     is desired.
    /// </param>
    /// <param name="head">The <c>VFunc</c> making up the head.</param>
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
      (toVar : 'Var -> Var)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (bodyExpr : BoolExpr<'Var>)
      (bodyView : GView<'Var>)
      (head : VFunc<'Var>)
      : Result<Z3.BoolExpr option, Error> =
        // We use a _lot_ of traversals in this function!
        let toVarTrav : Traversal<CTyped<'Var>, Expr<Var>, Error, unit> =
            tliftToExprDest
                (tliftOverCTyped (ignoreContext (toVar >> ok)))
        let toVarTravExpr = tliftToExprSrc toVarTrav
        let toVarTravBool = tliftToBoolSrc toVarTrav
        let toVarTravGView = tchainM (tliftOverGFunc toVarTravExpr) id
        let toVarTravVFunc = tliftOverFunc toVarTravExpr

        let findVarTrav : Traversal<TypedVar, Expr<Var>, Error, Var> =
            tliftToExprDest collectVars
        let findVarTravExpr = tliftToExprSrc findVarTrav
        let findVarTravBool = tliftToBoolSrc findVarTrav
        let findVarTravGView = tchainM (tliftOverGFunc findVarTravExpr) id
        let findVarTravVFunc = tliftOverFunc findVarTravExpr

        trial {
            // First, make everything use string variables.
            let! bodyExpr' =
                mapMessages Traversal (mapTraversal toVarTravBool (mkTypedSub normalRec bodyExpr))
            let! bodyView' =
                mapMessages Traversal (mapTraversal toVarTravGView bodyView)
            let! head' =
                mapMessages Traversal (mapTraversal toVarTravVFunc head)

            // Then, collect those variables.
            let! bodyExprVars =
                mapMessages Traversal (findVars findVarTravBool (mkTypedSub normalRec bodyExpr'))
            let! bodyViewVars =
                mapMessages Traversal (findVars findVarTravGView bodyView')
            let! headVars =
                mapMessages Traversal (findVars findVarTravVFunc head')

            // Now convert the variables to Z3 constants.
            let varToConst (var : TypedVar) =
                ctx.MkConst (valueOf var, typeToSort reals ctx (typeOf var))
            // We use a set here so that we don't quantify over variables twice.
            let varSet = Set.unionMany [ bodyExprVars; bodyViewVars; headVars ]
            let varConstSet = Set.map varToConst varSet
            let vars = Set.toArray varConstSet

            let bodyExprZ = boolToZ3 reals id ctx (mkTypedSub normalRec bodyExpr')

            let bodyZ =
                if (Multiset.length bodyView = 0)
                then bodyExprZ
                else
                    ctx.MkAnd
                        [| bodyExprZ
                           translateGView reals id ctx funcDecls bodyView' |]

            let headZ = translateVFunc reals id ctx funcDecls head'

            return mkQuantifiedEntailment ctx vars bodyZ headZ
        }

    (*
     * Deferred checks
     *)

    /// Converts a downclosure func into a guarded func, instantiating the
    /// variables directly as nonsymbolic unmarked vars.
    /// We map any instance of the iterator through f.
    let instantiate (iterator : Var) (f : Var -> IntExpr<Var>) (dfunc : DFunc) : GFunc<Var> =
        let trans param =
            match param with
            | Int (t, var) when var = iterator -> Int (t, f var)
            | v -> mkVarExp v
        gfunc BTrue dfunc.Name (List.map trans dfunc.Params)

    /// Converts a downclosure func into an ordinary func, instantiating the
    /// variables directly as nonsymbolic unmarked vars.
    /// We map any instance of the iterator through f.
    let instantiateFunc (iterator : Var) (f : Var -> IntExpr<Var>) (dfunc : DFunc) : Func<Expr<Var>> =
        let trans param =
            match param with
            | Int (t, var) when var = iterator -> Int (t, f var)
            | v -> mkVarExp v
        func dfunc.Name (List.map trans dfunc.Params)

    /// <summary>
    ///     Constructs a rule for a base downclosure check on a given func.
    /// </summary>
    let translateBaseDownclosure
      (reals : bool)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (svars : VarMap)
      (func : IteratedDFunc) 
      (defn : BoolExpr<Sym<Var>> option)
      (reason : string)
      : Result<(string * Z3.BoolExpr) option, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        let svarSeq = VarMap.toTypedVarSeq svars

        let iterVarR =
            // TODO(CaptainHayashi): subtypes?
            match func.Iterator with
            | Some (Int (_, x)) -> ok x
            | _ ->
                let check = NeedsBaseDownclosure (func, defn, reason)
                fail (CannotCheckDeferred (check, "malformed iterator"))

        (* TODO(CaptainHayashi): We're given the func needing downclosure in
           unflattened form.  This is kind-of messy, as we now have to flatten
           it again. *)
        // TODO(CaptainHayashi): this duplicates the HSF work a lot.
        let flatDFunc = Starling.Flattener.flattenDView svarSeq [func]
        let zeroFuncR =
            lift (fun it -> instantiateFunc it (fun _ -> IInt 0L) flatDFunc)
                iterVarR

        // TODO(CaptainHayashi): using a round peg in a square hole here.
        let empFunc =
            Multiset.singleton (gfunc BTrue "emp" (Seq.map mkVarExp svarSeq))

        let ruleR =
            bind
                (fun zeroFunc ->
                    mkRule reals id ctx funcDecls BTrue empFunc zeroFunc)
                zeroFuncR

        lift (Option.map (mkPair (sprintf "_baseD_%s" func.Func.Name)))
            ruleR

    /// <summary>
    ///     Constructs a rule for an inductive downclosure check on a given
    ///     func.
    /// </summary>
    let translateInductiveDownclosure
      (reals : bool)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (svars : VarMap)
      (func : IteratedDFunc)
      (defn : BoolExpr<Sym<Var>> option)
      (reason : string)
      : Result<(string * Z3.BoolExpr) option, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        let svarSeq = VarMap.toTypedVarSeq svars

        // See above for caveats.
        let iterVarResult =
            // TODO(CaptainHayashi): subtypes?
            match func.Iterator with
            | Some (Int (_, x)) -> ok x
            | _ ->
                let check = NeedsInductiveDownclosure (func, defn, reason)
                fail (CannotCheckDeferred (check, "malformed iterator"))

        let flatDFunc = Starling.Flattener.flattenDView svarSeq [func]

        let normFuncResult =
            ok (vfunc flatDFunc.Name (List.map mkVarExp flatDFunc.Params))
        let succFuncResult =
            lift (fun it -> instantiate it incVar flatDFunc) iterVarResult
        let succViewResult = lift Multiset.singleton succFuncResult
        let guardResult =
            lift (fun it -> mkIntGe (IVar it) (IInt 0L)) iterVarResult

        let ruleResult =
            bind3
                (mkRule reals id ctx funcDecls)
                guardResult
                succViewResult
                normFuncResult

        lift (Option.map (mkPair (sprintf "_indD_%s" func.Func.Name)))
            ruleResult

    /// <summary>
    ///     Constructs a MuZ3 rule for a deferred check, if possible.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">The Z3 context to use to model the rule.</param>
    /// <param name="funcs">A map of active view <c>FuncDecl</c>s.</param>
    /// <param name="svars">Map of shared variables in the program.</param>
    /// <param name="check">The deferred check to translate.</param>
    /// <returns>
    ///     If successful, an optional pair of the constructed rule's name
    ///     and body.
    /// </returns>
    let translateDeferredCheck
      (reals : bool)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (svars : VarMap)
      (check : DeferredCheck)
      : Result<(string * Z3.BoolExpr) option, Error> =
        match check with
        | NeedsBaseDownclosure (func, defn, reason) ->
            translateBaseDownclosure reals ctx funcDecls svars func defn reason
        | NeedsInductiveDownclosure (func, defn, reason) ->
            translateInductiveDownclosure reals ctx funcDecls svars func defn reason

    (*
     * Variables
     *)

    /// <summary>
    ///     Constructs a rule for initialising a variable.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">The Z3 context to use to model the rule.</param>
    /// <param name="funcs">A map of active view <c>FuncDecl</c>s.</param>
    /// <param name="svars">Map of shared variables in the program.</param>
    /// <returns>
    ///     A sequence containing at most one pair of <c>string</c> and
    ///     Z3 <c>BoolExpr</c> representing the variable initialisation rule.
    /// </returns>
    let translateVariables
      (reals : bool)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (svars : VarMap) =
        let vpars =
            svars
            |> Map.toList
            |> List.map (fun (v, t) -> mkVarExp (withType t v))

        let defaultVal =
            function
            | Expr.Int (t, _) -> ok (Expr.Int (t, IInt 0L))
            | Expr.Bool (t, _) -> ok (Expr.Bool (t, BFalse))
            (* TODO(CaptainHayashi): this needs implementing.
               Will requires array literal support. *)
            | Expr.Array _ -> fail ArraysNotSupported

        // TODO(CaptainHayashi): actually get these initialisations from
        // somewhere.
        let bodyResult =
            vpars
            |> List.map
                   (fun v ->
                        let dResult = defaultVal v
                        lift (fun d -> BEq (v, d)) dResult)
            |> collect
            |> lift mkAnd

        let head = { Name = "emp" ; Params = vpars }

        let ruleResult =
            bind
                (fun body ->
                    mkRule reals id ctx funcDecls body Multiset.empty head)
                bodyResult
        lift (maybe Seq.empty (fun x -> Seq.singleton ("init", x))) ruleResult


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
    let translateTerm
      (reals : bool)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (name : string, {Cmd = c ; WPre = w ; Goal = g} : CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>)
      : Result<(string * Z3.BoolExpr) option, Error> =
        let ruleResult = mkRule reals unmarkVar ctx funcDecls c.Semantics w g
        lift (Option.map (mkPair name)) ruleResult  // TODO: keep around Command?

    /// <summary>
    ///     Constructs muZ3 rules and goals for a model.
    /// </summary>
    /// <param name="reals">
    ///     Whether to use Real instead of Int for integers.
    /// </param>
    /// <param name="ctx">
    ///     The Z3 context to use for modelling the fixpoint.
    /// </param>
    /// <param name="_arg1">The model to turn into a fixpoint.</param>
    /// <returns>
    ///     A Chessie result wrapping, on success, a <see cref="MuModel"/>
    ///     containing the translation of the Starling model to MuZ3.
    /// </returns>
    let translate
      (reals : bool)
      (ctx : Z3.Context)
      ({ SharedVars = svars; ViewDefs = ds; Axioms = xs; DeferredChecks = cs }
         : Model<CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>,
                 FuncDefiner<BoolExpr<Var> option>> )
      : Result<MuModel, Error> =
        let funcDecls, definites = translateViewDefs reals ctx ds
        let vrulesResult = translateVariables reals ctx funcDecls svars

        let axseq = Map.toSeq xs
        let tMaybeRulesResult =
            collect (Seq.map (translateTerm reals ctx funcDecls) axseq)
        let trulesResult = lift (Seq.choose id) tMaybeRulesResult

        let tdc = translateDeferredCheck reals ctx funcDecls svars
        let drulesResult = lift (Seq.choose id) (collect (Seq.map tdc cs))

        lift3
            (fun drules vrules trules ->
                { Definites = List.ofSeq definites
                  Rules = Map.ofSeq (Seq.concat [ drules; vrules; trules ])
                  FuncDecls = funcDecls })
            drulesResult
            vrulesResult
            trulesResult


/// <summary>
///     Proof execution using MuZ3.
/// </summary>
module Run =
    open Starling.Core.Z3.Expr

    /// <summary>
    ///     Generates the MuZ3 rules representing a definite view constraint.
    /// </summary>
    /// <param name="shouldUseRealsForInts">
    ///     Whether or not we should model integers using Z3 reals.
    /// </param>
    /// <param name="ctx">The Z3 context to use for modelling the rules.</param>
    /// <param name="funcDecls">
    ///     The map of <c>FuncDecl</c>s to use when creating view
    ///     applications.
    /// </param>
    /// <param name="fixedpoint">The MuZ3 fixedpoint to add rules to.</param>
    /// <param name="unsafeapp">The expression representing 'unsafe()'.</param>
    /// <param name="view">The view being defined, as a single func.</param>
    /// <param name="def">The view definition.</param>
    let genViewDefRule
      (shouldUseRealsForInts : bool)
      (ctx : Z3.Context)
      (funcDecls : Map<string, Z3.FuncDecl>)
      (fixedpoint : Z3.Fixedpoint)
      (unsafeapp : Z3.BoolExpr)
      (view : VFunc<Var>)
      (def : BoolExpr<Var>)
      : Result<unit, Error> =
        let tdef = mkTypedSub normalRec def

        (* To model a view definition, we introduce an if and only if.
           This can't be modelled directly in MuZ3, so instead we split it
           into two implications.

           This is the 'def => view' part. *)
        let defImpliesViewR =
            Translator.mkRule
                shouldUseRealsForInts id ctx funcDecls def Multiset.empty view
        let defImpliesViewAddR =
            lift (Option.iter fixedpoint.AddRule) defImpliesViewR

        // TODO(CaptainHayashi): de-duplicate this with mkRule?
        let defVarsR =
            findVars (tliftToBoolSrc (tliftToExprDest collectVars)) tdef
        let paramVarsR =
            findVars
                (tchainL (tliftOverExpr collectVars) id)
                view.Params
        let varsR =
            mapMessages Traversal
                (lift2 Set.union defVarsR paramVarsR)

        let z3VarsR =
              lift
                  (Set.map
                      (fun (var : CTyped<Var>) ->
                          ctx.MkConst
                              (valueOf var,
                               typeToSort shouldUseRealsForInts ctx (typeOf var)))
                   >> Set.toArray)
                  varsR

        (* This is the 'view => def' part.
           We can't model this directly in MuZ3 because the head of a MuZ3
           constraint must be a single positive func.
           Instead, we rearrange to 'view && !def => unsafe', where unsafe is
           a stand-in for some notion of false. *)
        // TODO(CaptainHayashi): in practice this appears to be unsound.
        let viewImpliesDefR =
            lift
                (fun z3Vars ->
                    Translator.mkQuantifiedEntailment
                        ctx
                        z3Vars
                        (ctx.MkAnd [| boolToZ3 shouldUseRealsForInts id ctx (mapTypedSub mkNot tdef)
                                      Translator.translateVFunc shouldUseRealsForInts id ctx funcDecls view |])
                        unsafeapp)
                z3VarsR
        lift2 (fun _ -> Option.iter fixedpoint.AddRule)
            defImpliesViewR
            viewImpliesDefR

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
    let fixgen
      (reals : bool)
      (ctx : Z3.Context)
      ({ Definites = ds; Rules = rs ; FuncDecls = fm } : MuModel)
      : Result<(Z3.Fixedpoint * Z3.FuncDecl), Error> =
        let fixedpoint = ctx.MkFixedpoint ()

        let pars = ctx.MkParams ()
        pars.Add("engine", ctx.MkSymbol("pdr"))
        fixedpoint.Parameters <- pars

        let unsafe = ctx.MkFuncDecl ("unsafe", [||], ctx.MkBoolSort () :> Z3.Sort)
        fixedpoint.RegisterRelation unsafe
        let unsafeapp = unsafe.Apply [| |] :?> Z3.BoolExpr

        let viewDefRulesResult =
            collect (List.map (uncurry (genViewDefRule reals ctx fm fixedpoint unsafeapp)) ds)

        lift (fun _ ->
            Map.iter (fun (s : string) g -> fixedpoint.AddRule (g, ctx.MkSymbol s :> Z3.Symbol)) rs
            Map.iter (fun _ g -> fixedpoint.RegisterRelation g) fm

            (fixedpoint, unsafe))
            viewDefRulesResult

    /// <summary>
    ///     Runs a MuZ3 fixedpoint.
    /// </summary>
    /// <param name="fixedpoint">The <c>Fixedpoint</c> to run.</param>
    /// <param name="unsafe">
    ///     The <c>FuncDecl</c> naming the unsafeness predicate.
    /// </param>
    /// <returns>
    ///     A <c>MuResult</c>.
    /// </returns>
    let run (fixedpoint : Z3.Fixedpoint) (unsafe : Z3.FuncDecl) : MuSat =
        match (fixedpoint.Query [| unsafe |]) with
        | Z3.Status.SATISFIABLE -> MuSat.Sat (fixedpoint.GetAnswer ())
        | Z3.Status.UNSATISFIABLE -> MuSat.Unsat (fixedpoint.GetAnswer ())
        | Z3.Status.UNKNOWN -> MuSat.Unknown (fixedpoint.GetReasonUnknown ())
        | _ -> MuSat.Unknown "query result out of bounds"

/// <summary>
///     The Starling MuZ3 backend driver.
/// </summary>
/// <param name="reals">
///     Whether to use Real instead of Int.
///     This can be faster, but is slightly inaccurate.
/// </param>
/// <param name="req">The request to handle.</param>
/// <returns>
///     A function implementing the chosen MuZ3 backend process.
/// </returns>
let run (reals : bool) (req : Request)
  : Model<CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>,
          FuncDefiner<BoolExpr<Var> option>>
    -> Result<Response, Error> =
    use ctx = new Z3.Context()
    match req with
    | Request.Translate ->
        Translator.translate reals ctx
        >> lift Response.Translate
    | Request.Fix ->
        Translator.translate reals ctx
        >> bind (Run.fixgen reals ctx >> lift Response.Fix)
    | Request.Sat ->
        Translator.translate reals ctx
        >> bind (Run.fixgen reals ctx >> lift (uncurry Run.run >> Response.Sat))
