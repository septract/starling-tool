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
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Sub
open Starling.Core.GuardedView


/// <summary>
///     Types used in func instantiation.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     Type of func instantiation tables.
    /// </summary>
    /// <typeparam name="defn">
    ///     Type of definitions of <c>Func</c>s stored in the table.
    ///     May be <c>unit</c>.
    /// </typeparam>
    type FuncTable<'defn> =
        // TODO(CaptainHayashi): this should probably be a map,
        // but translating it to one seems non-trivial.
        // Would need to define equality on funcs very loosely.
        (DFunc * 'defn) list

    /// <summary>
    ///     Type of Chessie errors arising from Instantiate.
    /// </summary>
    type Error =
        /// <summary>
        ///     The func looked up has a parameter <c>param</c>, which
        ///     has been assigned to an argument of the incorrect type
        ///     <c>atype</c>.
        /// </summary>
        | TypeMismatch of param: Param * atype: Type
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
        | UnwantedSym of sym: Func<Expr<Sym<MarkedVar>>>

    (* TODO(CaptainHayashi): these two shouldn't be in here, but
       they are, due to a cyclic dependency on Model and FuncTable. *)

    /// <summary>
    ///     A <c>Model</c> whose view definitions form an indefinite
    ///     <c>FuncTable</c>.
    /// </summary>
    /// <typeparam name="axiom">
    ///     Type of program axioms.
    /// </typeparam>
    type IFModel<'axiom> = Model<'axiom, FuncTable<MBoolExpr option>>

    /// <summary>
    ///     A <c>Model</c> whose view definitions form a definite
    ///     <c>FuncTable</c>.
    /// </summary>
    /// <typeparam name="axiom">
    ///     Type of program axioms.
    /// </typeparam>
    type DFModel<'axiom> = Model<'axiom, FuncTable<MBoolExpr>>


/// <summary>
///     Pretty printers used in func instantiation.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Expr.Pretty

    /// <summary>
    ///     Pretty-prints <c>FuncTable</c>s over <c>MBoolExpr</c>s.
    /// </summary>
    /// <param name="ft">
    ///     The <c>FuncTable</c> to print.
    /// </param>
    /// <returns>
    ///     A sequence of <c>Command</c>s representing the
    ///     pretty-printed form of <paramref name="ft"/>.
    /// </returns>
    let printFuncTable ft : Command seq =
        ft
        |> List.map (fun (v, d) -> colonSep [ printDFunc v
                                              printMBoolExpr d ] )
        |> List.toSeq

    /// <summary>
    ///     Pretty-prints a model view for a <c>DFModel</c>.
    /// </summary>
    /// <param name="pAxiom">
    ///     Pretty printer for axioms.
    /// </param>
    /// <returns>
    ///     A function, taking a <c>ModelView</c> and <c>DFModel</c>, and
    ///     returning a <c>Command</c>.
    /// </returns>
    let printDFModelView pAxiom =
        printModelView pAxiom printFuncTable

    /// Pretty-prints instantiation errors.
    let printError =
        function
        | TypeMismatch (par, atype) ->
            fmt "parameter '{0}' conflicts with argument of type '{1}'"
                [ printParam par; printType atype ]
        | CountMismatch (fn, dn) ->
            fmt "view usage has {0} parameter(s), but its definition has {1}"
                [ fn |> sprintf "%d" |> String; dn |> sprintf "%d" |> String ]
        | IndefiniteConstraint (view) ->
            fmt "indefinite 'constraint {0} -> ?' not allowed here"
                [ printDFunc view ]
        | UnwantedSym sym ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            fmt "encountered uninterpreted symbol {0}"
                [ printSym (constToString >> String) (Sym sym) ]


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
let checkParamCount func =
    function
    | None -> ok None
    | Some def ->
        let fn = List.length func.Params
        let dn = List.length (fst def).Params
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
let lookup func =
    // First, try to find a func whose name agrees with ours.
    Seq.tryFind (fun (dfunc, _) -> dfunc.Name = func.Name)
    >> checkParamCount func

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
              | (Int _, ((Bool _) as param)) -> TypeMismatch (param, Int ()) |> fail
              | (Bool _, ((Int _) as param)) -> TypeMismatch (param, Bool ()) |> fail
              | _ -> ok ()))
        func.Params
        def.Params
    |> collect
    |> lift (fun _ -> func)

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
/// <param name="liftSrcVar">
///     A partial function lifting the source variable type to
///     <c>string</c>s.  Any variable not mapped by this function
///     is instead mapped by <c>passSrcVar</c>.
/// </param>
/// <param name="passSrcVar">
///     A function directly converting source to destination
///     variable types.
/// </param>
/// <param name="_arg1">
///     The func providing the arguments to substitute.
/// </param>
/// <param name="_arg2">
///     The <c>DFunc</c> into which we are substituting.
/// </param>
/// <typeparam name="srcVar">
///     The type of variables in the parameters being substituted into.
/// </typeparam>
/// <typeparam name="dstVar">
///     The type of variables in the arguments being substituted.
/// </typeparam>
/// <returns>
///     A <c>VSubFun</c> performing the above substitutions.
/// </returns>
let paramSubFun
  (liftSrcVar : 'srcVar -> string option)
  (passSrcVar : 'srcVar -> 'dstVar)
  ( { Params = fpars } : VFunc<'dstVar>)
  ( { Params = dpars } : DFunc)
  : VSubFun<'srcVar, 'dstVar> =
    let pmap =
        Seq.map2 (fun par up -> valueOf par, up) dpars fpars
        |> Map.ofSeq

    Mapper.make
        (fun srcV ->
             match (Option.bind pmap.TryFind (liftSrcVar srcV)) with
             | Some (Typed.Int expr) -> expr
             | Some _ -> failwith "param substitution type error"
             | None -> AVar (passSrcVar srcV))
        (fun srcV ->
             match (Option.bind pmap.TryFind (liftSrcVar srcV)) with
             | Some (Typed.Bool expr) -> expr
             | Some _ -> failwith "param substitution type error"
             | None -> BVar (passSrcVar srcV))

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
  : VSubFun<Sym<MarkedVar>, Sym<MarkedVar>> =
    liftVToSym
        (paramSubFun 
            (function Unmarked str -> Some str | _ -> None)
            Reg
            smvfunc
            dfunc)

/// <summary>
///     Produces a parameter substitution <c>VSubFun</c> from
///     <c>MVFunc</c>s.
/// </summary>
/// <param name="_arg1">
///     The <c>MVFunc</c> providing the arguments to substitute.
/// </param>
/// <param name="_arg2">
///     The <c>DFunc</c> into which we are substituting.
/// </param>
/// <returns>
///     A <c>VSubFun</c> performing the above substitutions.
/// </returns>
let mvParamSubFun
  (mvfunc : MVFunc)
  (dfunc : DFunc)
  : VSubFun<MarkedVar, MarkedVar> =
    (paramSubFun 
        (function Unmarked str -> Some str | _ -> None)
        id
        mvfunc
        dfunc)

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
                     Mapper.mapBool (onVars (psf vfunc dfunc)) defn))

/// <summary>
///     Functions for view definition filtering.
/// </summary>
module ViewDefFilter =
    /// <summary>
    ///     Tries to remove symbols from <c>ViewDef</c>s.
    /// </summary>
    let tryRemoveViewDefSymbols
      (defs : FuncTable<SMBoolExpr>)
      : Result<FuncTable<MBoolExpr>, Error> = 
        // TODO(CaptainHayashi): proper doc comment.
        // TODO(CaptainHayashi): stop assuming FuncTable is a list.
        defs
        |> List.map
               (fun (f, d) ->
                    d
                    |> Mapper.mapBool (tsfRemoveSym UnwantedSym)
                    |> lift (mkPair f))
        |> collect

    
    /// <summary>
    ///     Converts a <c>ViewDef</c> list into a <c>FuncTable</c> of possibly
    ///     indefinite views.
    /// </summary>
    let filterIndefiniteViewDefs
      (vds : SMBViewDef<DFunc> list)
      : Result<FuncTable<MBoolExpr option>, Error> =
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
      (vds : SMBViewDef<DFunc> list)
      : Result<FuncTable<MBoolExpr>, Error> =
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
    ///     definitions.  The new model is an <c>IFModel</c>.
    /// </returns>
    let filterModelIndefinite
      (model : UFModel<Term<SMBoolExpr, SMGView, SMVFunc>> )
      : Result<IFModel<Term<MBoolExpr, MGView, MVFunc>>, Error> =
        model
        |> tryMapAxioms (trySubExprInDTerm (tsfRemoveSym UnwantedSym))
        |> bind (tryMapViewDefs filterIndefiniteViewDefs)

    /// <summary>
    ///     Tries to convert a <c>ViewDef</C> based model into a
    ///     definite one.  The conversion fails if the model has any
    ///     indefinite constraints.
    /// </summary>
    /// <param name="model">
    ///     A model over <c>ViewDef</c>s.
    /// </param>
    /// <returns>
    ///     A <c>Result</c> over <c>Error</c> containing the
    ///     new model if the original contained only definite view
    ///     definitions.  The new model is a <c>DFModel</c>.
    /// </returns>
    let filterModelDefinite
      (model : UFModel<Term<SMBoolExpr, SMGView, SMVFunc>> )
      : Result<DFModel<Term<MBoolExpr, MGView, MVFunc>>, Error> =
        model
        |> tryMapAxioms (trySubExprInDTerm (tsfRemoveSym UnwantedSym))
        |> bind (tryMapViewDefs filterDefiniteViewDefs)
