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
open Starling.Core.TypeSystem
open Starling.Core.TypeSystem.Check
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
    ///     Type of Chessie errors arising from Instantiate.
    /// </summary>
    type Error =
        /// <summary>
        ///     The func looked up has a parameter <c>param</c>, which
        ///     has been assigned to an argument of the incorrect type
        ///     <c>atype</c>.
        /// </summary>
        | TypeMismatch of param: TypedVar * atype: Type
        /// <summary>
        ///     The func looked up has <c>fn</c> arguments, but its
        ///     definition has <c>dn</c> parameters.
        /// </summary>
        | CountMismatch of fn: int * dn: int
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

    (* TODO(CaptainHayashi): these two shouldn't be in here, but
       they are, due to a cyclic dependency on Model and FuncTable. *)

    /// <summary>
    ///     A view definition function implemented as an indefinite
    ///     <c>FuncTable</c> with no symbols.
    /// </summary>
    type FuncToIndefiniteBoolDefiner = FuncTable<VBoolExpr option>

    /// <summary>
    ///     A view definition function implemented as a definite
    ///     <c>FuncTable</c> with no symbols.
    /// </summary>
    type FuncToBoolDefiner = FuncTable<VBoolExpr>


/// <summary>
///     Pretty printers used in func instantiation.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.View.Pretty

    /// <summary>
    ///     Pretty-prints <c>FuncTable</c>s.
    /// </summary>
    /// <param name="pDefn">
    ///     Pretty printer for definitions.
    /// </param>
    /// <param name="ft">
    ///     The <c>FuncTable</c> to print.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of definitions in the <c>FuncTable</c>.
    /// </typeparam>
    /// <returns>
    ///     A sequence of <c>Command</c>s representing the
    ///     pretty-printed form of <paramref name="ft"/>.
    /// </returns>
    let printFuncTable
      (pDefn : 'defn -> Doc)
      (ft : FuncTable<'defn>)
      : Doc seq =
        ft
        |> List.map (fun (v, d) -> colonSep [ printDFunc v; pDefn d ] )
        |> List.toSeq

    /// <summary>
    ///     Pretty-prints a <see cref="FuncToBoolDefiner"/>.
    /// </summary>
    let printFuncToBoolDefiner : FuncToBoolDefiner -> Doc seq =
        printFuncTable printVBoolExpr

    /// <summary>
    ///     Pretty-prints a <see cref="FuncToIndefiniteBoolDefiner"/>.
    /// </summary>
    let printFuncToIndefiniteBoolDefiner : FuncToIndefiniteBoolDefiner -> Doc seq =
        printFuncTable
            (fun x -> withDefault (String "?") (Option.map printVBoolExpr x))

    /// Pretty-prints instantiation errors.
    let printError =
        function
        | TypeMismatch (par, atype) ->
            fmt "parameter '{0}' conflicts with argument of type '{1}'"
                [ printTypedVar par; printType atype ]
        | CountMismatch (fn, dn) ->
            fmt "view usage has {0} parameter(s), but its definition has {1}"
                [ fn |> sprintf "%d" |> String; dn |> sprintf "%d" |> String ]
        | IndefiniteConstraint (view) ->
            fmt "indefinite 'constraint {0} -> ?' not allowed here"
                [ printDFunc view ]
        | UnwantedSym sym ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            fmt "encountered uninterpreted symbol {0}"
                [ String sym ]


(*
 * Building FuncTables
 *)

/// <summary>
///     Builds a <c>FuncTable</c> from a sequence of pairs of <c>Func</c>
///     and definition.
/// </summary>
/// <param name="fseq">
///     The sequence of (<c>Func</c>, <c>'defn</c>) pairs.
/// </param>
/// <typeparam name="defn">
///     The type of <c>Func</c> definitions.  May be <c>unit</c>.
/// </typeparam>
/// <returns>
///     A <c>FuncTable</c> allowing the <c>'defn</c>s of the given <c>Func</c>s
///     to be looked up.
/// </returns>
let makeFuncTable fseq : FuncTable<'defn> =
    // This function exists to smooth over any changes in FuncTable
    // representation we make later (eg. to maps).
    Seq.toList fseq

/// <summary>
///     Creates a <c>FuncTable</c> from a sequence of <c>ViewDef</c>s.
/// </summary>
/// <param name="viewdefs">
///     The view definitions to use to create the <c>FuncTable</c>.
/// </param>
/// <returns>
///     A tuple of a <c>FuncTable</c>, and a list of <c>DFunc</c>s with
///     indefinite constraints.
/// </returns>
let funcTableFromViewDefs viewdefs =
    let rec buildLists definites indefinites viewdefs' =
        match viewdefs' with
        | [] -> (makeFuncTable definites, indefinites)
        | (Indefinite v) :: vs ->
            buildLists definites (v :: indefinites) vs
        | (Definite (v, s)) :: vs ->
            buildLists ((v, s) :: definites) indefinites vs
    buildLists [] [] viewdefs

/// <summary>
///     Returns the <c>Func</c>s contained in a <c>FuncTable</c>.
/// </summary>
/// <param name="ftab">
///     The <c>FuncTable</c> to break apart.
/// </param>
/// <typeparam name="defn">
///     The type of <c>Func</c> definitions.  May be <c>unit</c>.
/// </typeparam>
/// <returns>
///     A sequence of <c>Func</c>s contained in <paramref name="ftab" />.
/// </returns>
let funcsInTable (ftab : FuncTable<'defn>) =
    Seq.map fst ftab


(*
 * Func lookup
 *)

/// <summary>
///     Checks whether <c>func</c> and <c>_arg1</c> agree on parameter
///     count.
/// </summary>
/// <param name="func">
///     The func being looked up, the process of which this check is part.
/// </param>
/// <param name="_arg1">
///     An <c>Option</c>al pair of <c>DFunc</c> and its defining
///     <c>BoolExpr</c>.
///     The value <c>None</c> suggests that <c>func</c> has no definition,
///     which can be ok (eg. if the <c>func</c> is a non-defining view).
/// </param>
/// <returns>
///     A Chessie result, where the <c>ok</c> value is the optional pair of
///     prototype func and definition, and the failure value is a
///     <c>Starling.Instantiate.Error</c>.
/// </returns>
let checkParamCount (func : Func<'a>) : (Func<'b> * 'c) option -> Result<(Func<'b> * 'c) option, Error> =
    function
    | None -> ok None
    | Some def ->
        let fn = List.length func.Params
        let dn = List.length (fst def).Params
        if fn = dn then ok (Some def) else CountMismatch (fn, dn) |> fail

let checkParamCountPrim : PrimCommand -> PrimSemantics option -> Result<PrimSemantics option, Error> =
    fun prim opt ->
    match opt with
    | None -> ok None
    | Some def ->
        let fn = List.length prim.Args
        let dn = List.length def.Args
        if fn = dn then ok (Some def) else CountMismatch (fn, dn) |> fail
/// <summary>
///     Look up <c>func</c> in <c>_arg1</c>.
///
///     <para>
///         This checks that the use of <c>func</c> agrees on the number of
///         parameters, but not necessarily types.  You will need to add
///         type checking if needed.
///     </para>
/// </summary>
/// <param name="func">
///     The func to look up in <c>_arg1</c>.
/// </param>
/// <param name="_arg1">
///     An associative sequence mapping <c>Func</c>s to some definition.
/// </param>
/// <returns>
///     A Chessie result, where the <c>ok</c> value is an <c>Option</c>
///     containing the pair of
///     prototype func and definition, and the failure value is a
///     <c>Starling.Instantiate.Error</c>.  If the <c>ok</c> value is
///     <c>None</c>, it means no (valid or otherwise) definition exists.
/// </returns>
let lookup (func : Func<'a>) : seq<DFunc * 'b> -> Result<(DFunc * 'b) option, Error> =
    // First, try to find a func whose name agrees with ours.
    Seq.tryFind (fun (dfunc, _) -> dfunc.Name = func.Name)
    >> checkParamCount func

let lookupPrim : PrimCommand -> PrimSemanticsMap -> Result<PrimSemantics option, Error>  =
    fun prim map ->
    checkParamCountPrim prim
    <| Map.tryFind prim.Name map

/// <summary>
///     Checks whether <c>func</c> and <c>_arg1</c> agree on parameter
///     types.
/// </summary>
/// <param name="func">
///     The func being looked up, the process of which this check is part.
/// </param>
/// <param name="def">
///     The <c>DFunc</c> that <paramref name="func" /> has matched.
/// </param>
/// <returns>
///     A Chessie result, where the <c>ok</c> value is
///     <paramref name="func" />, and the failure value is a
///     <c>Starling.Instantiate.Error</c>.
/// </returns>
let checkParamTypes func def =
    List.map2
        (curry
             (function
              | UnifyInt _ | UnifyBool _ -> ok ()
              | UnifyFail (fp, dp) -> fail (TypeMismatch (dp, typeOf fp))))
        func.Params
        def.Params
    |> collect
    |> lift (fun _ -> func)

let checkParamTypesPrim : PrimCommand -> PrimSemantics -> Result<PrimCommand, Error> = 
    fun prim sem -> 
    List.map2
        (curry
             (function
              | UnifyInt _ | UnifyBool _ -> ok ()
              | UnifyFail (fp, dp) -> fail (TypeMismatch (dp, typeOf fp))))
        prim.Args
        sem.Args
    |> collect
    |> lift (fun _ -> prim)

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

let paramToMExpr =
    function
    | Int  i -> After i |> Reg |> AVar |> Int
    | Bool b -> After b |> Reg |> BVar |> Bool

let primParamSubFun
  ( cmd : PrimCommand )
  ( sem : PrimSemantics )
  : VSubFun<Var, Sym<MarkedVar>> =
    /// merge the pre + post conditions
    let fres = List.map paramToMExpr cmd.Results
    let fpars = cmd.Args @ fres
    let dpars = sem.Args @ sem.Results

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
///     Produces a parameter substitution <c>VSubFun</c> from
///     <c>SMVFunc</c>s.
/// </summary>
/// <param name="_arg1">
///     The <c>SMVFunc</c> providing the arguments to substitute.
/// </param>
/// <param name="_arg2">
///     The <c>DFunc</c> into which we are substituting.
/// </param>
/// <returns>
///     A <c>VSubFun</c> performing the above substitutions.
/// </returns>
let smvParamSubFun
  (smvfunc : SMVFunc)
  (dfunc : DFunc)
  : VSubFun<Sym<Var>, Sym<MarkedVar>> =
    liftVToSym (paramSubFun smvfunc dfunc)

let primSubFun prim sem = liftVToSym (primParamSubFun prim sem)

/// <summary>
///     Look up <c>func</c> in <c>_arg1</c>, and instantiate the
///     resulting Boolean expression, substituting <c>func.Params</c>
///     for the parameters in the expression.
/// </summary>
/// <param name="psf">
///     A function building the <c>VSubFun</c> used to map variables in
///     the expression, either by substituting in the arguments of the
///     func, or by transforming them to the correct variable type.
/// </param>
/// <param name="ftab">
///     The <c>FuncTable</c> whose definition for <c>func</c> is to be
///     instantiated.
/// </param>
/// <param name="vfunc">
///     The <c>VFunc</c> whose arguments are to be substituted into
///     its definition in <c>_arg1</c>.
/// </param>
/// <typeparam name="srcVar">
///     The type of the variables before substitution, ie in
///     <paramref name="expr"/>.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of the variables before substitution, ie in
///     <paramref name="expr"/>.
/// </typeparam>
/// <returns>
///     The instantiation of <c>func</c> as an <c>Option</c>al
///     <c>SMBoolExpr</c> wrapped inside a Chessie result.
/// </returns>
let instantiate
  (psf : VFunc<'dstVar> -> DFunc -> VSubFun<'srcVar, 'dstVar>)
  (ftab : FuncTable<BoolExpr<'srcVar>>)
  (vfunc : VFunc<'dstVar>)
  : Result<BoolExpr<'dstVar> option, Error> =
    ftab
    |> lookup vfunc
    |> bind
           (function
            | None -> ok None
            | Some (dfunc, defn) ->
                lift
                    (fun _ -> Some (dfunc, defn))
                    (checkParamTypes vfunc dfunc))
    |> lift
           (Option.map
                (fun (dfunc, defn) ->
                     Mapper.mapBoolCtx (onVars (psf vfunc dfunc)) NoCtx defn |> snd))

let instantiatePrim
  (psf : PrimCommand -> PrimSemantics -> VSubFun<Sym<Var>, Sym<MarkedVar>>)
  (ftab : PrimSemanticsMap)
  (vfunc : PrimCommand)
  : Result<SMBoolExpr option, Error> =
    lookupPrim vfunc ftab
    |> bind
           (function
            | None -> ok None
            | Some sem ->
                lift
                    (fun _ -> Some sem)
                    (checkParamTypesPrim vfunc sem))
    |> lift
           (Option.map
                (fun sem ->
                     let mapper = onVars <| psf vfunc sem
                     Mapper.mapBoolCtx mapper NoCtx sem.Body |> snd))

/// <summary>
///     Functions for view definition filtering.
/// </summary>
module ViewDefFilter =
    /// <summary>
    ///     Tries to remove symbols from <c>ViewDef</c>s.
    /// </summary>
    let tryRemoveViewDefSymbols
      (defs : FuncTable<SVBoolExpr>)
      : Result<FuncTable<VBoolExpr>, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        // TODO(CaptainHayashi): stop assuming FuncTable is a list.
        defs
        |> List.map
               (fun (f, d) ->
                    d
                    |> Mapper.mapBoolCtx (tsfRemoveSym UnwantedSym) NoCtx
                    |> snd
                    |> lift (mkPair f))
        |> collect


    /// <summary>
    ///     Converts a <c>ViewDef</c> list into a <c>FuncTable</c> of possibly
    ///     indefinite views.
    /// </summary>
    let filterIndefiniteViewDefs
      (vds : SVBViewDef<DFunc> list)
      : Result<FuncToIndefiniteBoolDefiner, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        vds
        |> funcTableFromViewDefs
        (* TODO(CaptainHayashi): defs is already a func table, so
           don't pretend it's just a list of tuples. *)
        |> function
           | (defs, indefs) ->
               defs
               |> tryRemoveViewDefSymbols
               |> lift
                      (fun defs' ->
                           makeFuncTable
                              (seq {
                                   for (v, d) in defs' do
                                       yield (v, Some d)
                                   for v in indefs do
                                       yield (v, None)
                               } ))

    /// <summary>
    ///     Converts a <c>ViewDef</c> list into a <c>FuncTable</c> of only
    ///     definite views.
    /// </summary>
    let filterDefiniteViewDefs
      (vds : SVBViewDef<DFunc> list)
      : Result<FuncToBoolDefiner, Error> =
        // TODO(CaptainHayashi): proper doc comment.
        vds
        |> funcTableFromViewDefs
        |> function
           | defs, [] ->
               tryRemoveViewDefSymbols defs
           | _, indefs ->
               indefs |> List.map IndefiniteConstraint |> Bad

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
      (model : Model<Term<SMBoolExpr, SMGView, SMVFunc>,
                     FuncToSymBoolDefiner> )
      : Result<Model<Term<MBoolExpr, MGView, MVFunc>,
                     FuncToIndefiniteBoolDefiner>, Error> =
        model
        |> tryMapAxioms (trySubExprInDTerm (tsfRemoveSym UnwantedSym) NoCtx >> snd)
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
    /// Produces the reification of an unguarded func.
    /// This corresponds to D^ in the theory.
    let interpretVFunc (ft : FuncTable<SVBoolExpr>) func =
        instantiate smvParamSubFun ft func
        |> lift (withDefault BTrue)  // Undefined views go to True by metatheory

    let interpretGFunc (ft : FuncTable<SVBoolExpr>) {Cond = c; Item = i} =
        interpretVFunc ft i
        |> lift (mkImplies c)

    /// Interprets an entire view application over the given functable.
    let interpretGView (ft : FuncTable<SVBoolExpr>) =
        Multiset.toFlatSeq
        >> Seq.map (interpretGFunc ft)
        >> collect
        >> lift Seq.toList
        >> lift mkAnd

    /// Interprets all of the views in a term over the given functable.
    let interpretTerm
      (ft : FuncTable<SVBoolExpr>)
      : Term<SMBoolExpr, SMGView, SMVFunc> -> Result<SFTerm, Error> =
        tryMapTerm ok (interpretGView ft) (interpretVFunc ft)


    /// <summary>
    ///     Converts all indefinite viewdefs to symbols.
    /// </summary>
    /// <param name="vs">
    ///     The view definitions to convert.
    /// </param>
    /// <returns>
    ///     A <c>FuncTable</c> mapping each view func to a
    ///     <c>SVBoolExpr</c> giving its definition.  Indefinite
    ///     viewdefs are represented by symbols.
    /// </returns>
    let symboliseIndefinites vs =
        // First, get the functable of all definite views.
        let def, indef = funcTableFromViewDefs vs

        // Then, convert the indefs to symbols.
        let symconv =
            Mapper.make (Reg >> AVar) (Reg >> BVar)

        let idsym : FuncTable<SVBoolExpr> =
            List.map
                (fun { Name = n ; Params = ps } ->
                    (func n ps,
                     BVar
                         (Sym
                              (func
                                   (sprintf "!UNDEF:%A" n)
                                   (List.map
                                       (Mapper.mapCtx symconv NoCtx >> snd)
                                       ps)))))
                indef

        // TODO(CaptainHayashi): use functables properly.
        def @ idsym


    /// <summary>
    ///     Run the instantiation phase.
    ///
    ///     <para>
    ///         This consumes the view definitions.
    ///     </para>
    /// </summary>
    /// <param name="model">
    ///     The model to instantiate.
    /// </param>
    /// <returns>
    ///     The model with all views instantiated.
    /// </returns>
    let run
      (model : Model<STerm<SMGView, SMVFunc>, FuncToSymBoolDefiner>)
      : Result<Model<SFTerm, unit>, Error> =
      let vs = symboliseIndefinites model.ViewDefs

      model
      |> tryMapAxioms (interpretTerm vs)
      |> lift (withViewDefs ())
