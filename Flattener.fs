/// <summary>
///     Part of the Starling tool that flattens terms, adding in globals.
/// </summary>
module Starling.Flattener

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.View
open Starling.Reifier
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Command
open Starling.Core.GuardedView


/// <summary>
///     Wrapper containing a goal view before flattening, and the
///     flattened result.
/// </summary>
/// <typeparam name="Flat">The type of the flattened result.</typeparam>
type Flattened<'Flat> =
    { Original : IteratedOView
      Flattened : 'Flat }

/// <summary>
///     Type of terms after complete flattening.
/// </summary>
/// <typeparam name="Var">The type of variables in the term.</typeparam>
type FlatTerm<'Var> when 'Var : equality and 'Var : comparison =
    Term<
        CommandSemantics<BoolExpr<'Var>>,
        Reified<GView<'Var>>,
        Flattened<Func<Expr<'Var>>>>


/// <summary>
///    Maps a function over a flattened view.
/// </summary>
/// <param name="f">The function to apply to the flattened view.</param>
/// <param name="view">The flattened view to map.</param>
/// <typeparam name="A">The original inner view type.</typeparam>
/// <typeparam name="B">The resulting inner view type.</typeparam>
/// <returns>
///     A new <see cref="Flattened"/> with the same original view, but
///     with the flattened view set to the result of running
///     <paramref name="f"/> over <paramref name="view"/>'s inner
///     reified view.
/// </returns>
let flattenedMap (f : 'A -> 'B) (view : Flattened<'A>) : Flattened<'B> =
    { Original = view.Original; Flattened = f view.Flattened }

/// <summary>
///     Pretty-prints the flattened component of a flattened view.
/// </summary>
/// <param name="pNewView">The printer for the wrapped view.</param>
/// <param name="v">The flattened view to print.</param>
/// <typeparam name="NewView">The type of the wrapped view.</typeparam>
/// <returns>
///     A <see cref="Doc"/> representing the flattened view.
/// </returns>
let printFlattened (pNewView : 'NewView -> Core.Pretty.Doc) (v : Flattened<'NewView>)
  : Core.Pretty.Doc =
    pNewView v.Flattened
 
module Traversal =
    open Starling.Core.Traversal
    open Starling.Core.Command.Traversal
    open Starling.Core.GuardedView.Traversal
    open Starling.Core.View.Traversal

    /// <summary>
    ///     Lifts a <c>Traversal</c> over all variables in a reified
    ///     <see cref="FlatTerm"/>.
    /// </summary>
    /// <param name="traversal">
    ///     The <c>Traversal</c> to map over all variables in the term.
    ///     This should map from typed variables to expressions.
    /// </param>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <typeparam name="SrcVar">The type of initial variables.</typeparam>
    /// <typeparam name="DstVar">The type of final variables.</typeparam>
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverFlatTerm
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
      : Traversal<FlatTerm<'SrcVar>, FlatTerm<'DstVar>, 'Error, 'Var> =
        fun ctx { Cmd = c ; WPre = w; Goal = g } ->
            let tCmd = tliftOverCommandSemantics traversal
            let tWPre = tchainM (tliftOverGFunc traversal) id
            let tGoal = tliftOverFunc traversal
            tchain3 tCmd tWPre tGoal
                (fun (c', wr, gr) ->
                    let w' = { Original = w.Original; Reified = wr }
                    let g' = { Original = g.Original; Flattened = gr }
                    { Cmd = c'; WPre = w'; Goal = g' })
                ctx
                (c, w.Reified, g.Flattened)

/// <summary>
///     Extracts a sequence of all of the parameters in a func sequence
/// </summary>
let paramsOfFuncSeq (funcs : Func<'var> seq) : 'var seq =
    Seq.collect (fun v -> v.Params) funcs

/// <summary>
///     Constructs a (hopefully) unique name for a Func resulting from
///     the flattening of a func sequence
/// </summary>
let genFlatFuncSeqName (funcs : Func<'var> seq) : string =
    funcs
    // These two steps are to ensure we don't capture an existing name.
    |> Seq.map (fun { Name = n } -> n.Replace("_", "__"))
    |> scons "v"
    |> String.concat "_"
    // This step ensures that the empty view is named 'emp', not 'v'.
    |> fun s -> if s = "v" then "emp" else s

let genFlatIteratedFuncName ifcs =
    let funcs = Seq.map (fun ifc -> ifc.Func) ifcs
    genFlatFuncSeqName funcs

let paramsFromIteratedFunc
  (funcContainer : IteratedContainer<Func<'Param>, 'Param option>)
  : 'Param list =
    let funcParams = funcContainer.Func.Params
    let iterParams = maybe [] (fun i -> [i]) funcContainer.Iterator
    iterParams @ funcParams

/// <summary>
///     Constructs a Func from a DView
/// </summary>
/// <param name="svars">
///     The set of shared variables in use, to be merged into the func.
/// </param>
/// <param name="dview">
///     The DView to use in construction.
/// </param>
/// <returns>
///     A new Func containing all parameters of the individuals as well as their iterators
///     with the shared variables appended
/// </returns>
let flattenDView (svars : TypedVar seq) (dview : DView) : DFunc =
    // TODO: What if iterators share names? e.g. iterated A [n] * iterated B [n]
    let ownParams = Seq.collect paramsFromIteratedFunc dview
    let allParams = Seq.append svars ownParams
    { Name = genFlatIteratedFuncName dview; Params = Seq.toList allParams }

/// Flattens an OView into an SMVFunc given the set of globals
let flattenOView (svarExprs : Expr<Sym<MarkedVar>> seq) (oview : OView)
  : SMVFunc =
    { Name = genFlatFuncSeqName oview
      Params = Seq.toList (Seq.append svarExprs (paramsOfFuncSeq oview)) }

/// <summary>
///     Flattens a term by converting all of its OViews into single funcs.
/// </summary>
/// <param name="globalsF">
///     A function that takes a marker (Before, After, etc.) and returns
///     a sequence of all global variables converted into symbolic marked
///     expressions with said marker.
/// </param>
/// <returns>
///     A function mapping terms over OViews to terms over SMVFuncs.
/// </returns>
let flattenTerm
  (globalsF : (Var -> MarkedVar) -> SMExpr seq)
  : Term<_, Reified<Set<GuardedSubview>>, Flattened<OView>>
  -> Term<_, Reified<GView<Sym<MarkedVar>>>, Flattened<SMVFunc>> =
    mapTerm id
            (reifyMap
                (Seq.map (mapItem (flattenOView (globalsF Before)))
                 >> Multiset.ofFlatSeq))
            (flattenedMap (flattenOView (globalsF After)))

/// <summary>
///    Flattens all func sequences in a model, turning them into funcs.
///    <para>
///        This allows each combination of views coming out of reification
///        to be represented by a single uninterpreted function, which can
///        then either be interpreted using the corresponding ViewDefs,
///        or inferred by using a solver like HSF.
///    </para>
/// </summary>
/// <param name="model">
///     The model to flatten.
/// </param>
/// <returns>
///     The flattened model.
/// </returns>
let flatten
  (model : Model<Term<_, Reified<Set<GuardedSubview>>, Flattened<OView>>,
                 ViewDefiner<SVBoolExpr option>>)
  : Model<Term<_, Reified<GView<Sym<MarkedVar>>>, Flattened<SMVFunc>>,
          FuncDefiner<SVBoolExpr option>> =
    /// Build a function making a list of global arguments, for view assertions.
    let globalsF marker = varMapToExprs (marker >> Reg) model.SharedVars

    /// Build a list of global parameters, for view definitions.
    let globalsP = VarMap.toTypedVarSeq model.SharedVars

    { Pragmata = model.Pragmata
      SharedVars = model.SharedVars
      ThreadVars = model.ThreadVars
      Axioms = Map.map (fun _ x -> flattenTerm globalsF x) model.Axioms
      ViewDefs =
          model.ViewDefs
          |> ViewDefiner.toSeq
          |> Seq.map (pairMap (flattenDView globalsP) id)
          |> FuncDefiner.ofSeq
      Semantics = model.Semantics
      ViewProtos = model.ViewProtos
      DeferredChecks = model.DeferredChecks }


/// Stage that flattens the Iterator's from GuardedFunc's
module Iter =
    open Starling.Core.Pretty

    /// <summary>
    ///     Type of errors that can occur during iterator lowering.
    /// </summary>
    type Error =
        /// <summary>
        ///     A func was lowered that doesn't have a valid prototype.
        /// </summary>
        | ProtoLookupError of FuncName : string
                            * Error : Starling.Core.Definer.Error
        /// <summary>
        ///     A func was lowered that doesn't have a prototype at all.
        /// </summary>
        | ProtoMissing of FuncName : string
        /// <summary>
        ///     A non-iterated func had a symbolic iterator.
        /// </summary>
        | CannotEvalIterator of Func : Func<Expr<Sym<MarkedVar>>>
                              * Iterator : IntExpr<Sym<MarkedVar>>

    /// <summary>
    ///     Pretty-prints an iterator lowering error.
    /// </summary>
    /// <param name="error">
    ///     The error to print.
    /// </param>
    /// <returns>
    ///     The <see cref="Doc"/> representing the error.
    /// </returns>
    let printError : Error -> Core.Pretty.Doc =
        function
        | ProtoLookupError (func, error) ->
            wrapped
                "prototype lookup for func"
                (String func)
                (Core.Definer.Pretty.printError error)
        | ProtoMissing func ->
            String "prototype missing for func" <+> quoted (String func)
        | CannotEvalIterator (func, iterator) ->
            String "non-iterated func"
            <+> quoted (Core.View.Pretty.printSMVFunc func)
            <+> String "is used with iterator"
            <+> quoted
                  (Core.Expr.Pretty.printIntExpr
                      (Core.Symbolic.Pretty.printSym
                           Core.Var.Pretty.printMarkedVar)
                      iterator) 
            <&> String "which cannot be resolved to an integer"

    /// <summary>
    ///     Decides whether a func should be interpreted as iterated by looking
    ///     at its prototype.
    /// </summary>
    /// <param name="protos">
    ///     The prototype definer used to check the iterated status.
    /// </param>
    /// <param name="func">
    ///     The func to check.
    /// </param>
    /// <returns>
    ///     Whether the func is iterated, wrapped in an error because lookup
    ///     in the prototypes can fail.
    /// </returns>
    let checkIterated
      (protos : FuncDefiner<ProtoInfo>)
      (func : Func<'Param>)
      : Result<bool, Error> =
            FuncDefiner.lookup func protos
            |> mapMessages (fun f -> ProtoLookupError (func.Name, f))
            |> bind
                (function
                 | None -> fail (ProtoMissing func.Name)
                 | Some (_, { IsIterated = isIterated }) -> ok isIterated)

    /// <summary>
    ///     Decides whether a func should be interpreted as iterated by looking
    ///     at its prototype, and then tries to calculate the number of times
    ///     it should be inserted into its parent view if not.
    /// </summary>
    /// <param name="protos">
    ///     The prototype definer used to check the iterated status.
    /// </param>
    /// <param name="func">
    ///     The func to check.
    /// </param>
    /// <param name="iterator">
    ///     The iterator expression that was attached to the func.  The presence
    ///     of this does not necessarily mean the func is supposed to be
    ///     iterated.  This is because previous stages can combine multiple
    ///     copies of a non-iterated func into one 'pseudo-iterated' func for
    ///     simplicity.
    /// </param>
    /// <returns>
    ///     None if the func is iterated (and should thus be lowered); Some n
    ///     if the func is not iterated (and should instead just be replicated
    ///     n times, where n was the value of the iterator).
    ///     Wrapped in an error because lookup in the prototypes, and
    ///     evaluating the func's iterator, can fail.
    /// </returns>
    let evalIteratorIfFuncNotIterated
      (protos : FuncDefiner<ProtoInfo>)
      (func : Func<Expr<Sym<MarkedVar>>>)
      (iterator : IntExpr<Sym<MarkedVar>>)
      : Result<int64 option, Error> =
        func
        |> checkIterated protos
        |> bind
            (function
             | true -> ok None
             | false ->
                // TODO(CaptainHayashi): evaluate this properly.
                match iterator with
                | IInt n -> ok (Some n)
                | i -> fail (CannotEvalIterator (func, i)))

    /// <summary>
    ///     Lowers an iterated DFunc, folding it into an accumulating view.
    ///     <para>
    ///         If the func matches an iterated prototype, we move the Iterator
    ///         Expression into the params; else, we try to expand it.
    ///     </para>
    /// </summary>
    let lowerIterDFunc
      : FuncDefiner<ProtoInfo> -> IteratedDFunc -> Result<DFunc, Error> =
        fun protos { Func = df; Iterator = it } ->
            df
            |> checkIterated protos
            |> lift
                (function
                 // TODO(CaptainHayashi): assuming n here is silly
                 | true -> dfunc df.Name (withDefault (Int (normalRec, "n")) it :: df.Params)
                 | false -> df)

    /// <summary>
    ///     Lowers an iterated SMVFunc into a list of SMVFuncs.
    ///     <para>
    ///         If the func matches an iterated prototype, we move the Iterator
    ///         Expression into the params; else, we try to expand it.
    ///     </para>
    /// </summary>
    let lowerIterSMVFunc
      : FuncDefiner<ProtoInfo>
      -> IteratedContainer<Func<Expr<Sym<MarkedVar>>>, IntExpr<Sym<MarkedVar>>>
      -> Result<Func<Expr<Sym<MarkedVar>>> list, Error> =
        fun protos { Func = vfunc; Iterator = it } ->
            evalIteratorIfFuncNotIterated protos vfunc it
            |> lift
                (function
                 | Some k -> [ for i in 1L .. k -> vfunc ]
                 | None ->
                    [ Starling.Collections.func vfunc.Name (Int (normalRec, it) :: vfunc.Params) ])

    /// flattens an entire IteratedSubview into a flat GView
    let lowerIteratedSubview
      : FuncDefiner<ProtoInfo>
      -> GuardedIteratedSubview -> Result<GuardedSubview, Error> =
        fun protos { Cond = c; Item = iterview } ->
            iterview
            |> List.map (lowerIterSMVFunc protos)
            |> collect
            |> lift (List.concat >> (fun m -> { Cond = c; Item = m }))

    /// flattens an entire IteratedOView into a flat OView
    /// with no iterators
    let lowerIteratedOView (protos : FuncDefiner<ProtoInfo>) (v : IteratedOView)
      : Result<Flattened<OView>, Error> =
        let flatR = collect (List.map (lowerIterSMVFunc protos) v)
        lift (fun flat -> { Original = v; Flattened = List.concat flat }) flatR

    /// Flattens both the W/Pre and the Goal of a Term, removing the Iterators
    /// and returning the new flattened Term
    let lowerIteratedTerm :
      FuncDefiner<ProtoInfo>
      -> Term<_, Reified<Set<GuardedIteratedSubview>>, IteratedOView>
      -> Result<Term<_, Reified<Set<GuardedSubview>>, Flattened<OView>>, Error> =
        fun proto ->
            let lowerIteratedSubviewSet =
                Set.toSeq
                >> Seq.map (lowerIteratedSubview proto)
                >> collect
                >> lift Set.ofSeq

            tryMapTerm
                ok
                (tryReifyMap lowerIteratedSubviewSet)
                (lowerIteratedOView proto)

    /// Flattens iterated guarded views in a model's terms down to guarded views
    /// taking iter[n] g(xbar...) to g(n, xbar...)
    /// and returning that new model
    let flatten
        (model : Model<Term<_, Reified<Set<GuardedIteratedSubview>>, IteratedOView>, _>)
            : Result<Model<Term<_, Reified<Set<GuardedSubview>>, Flattened<OView>>, _>, Error> =
        tryMapAxioms (lowerIteratedTerm model.ViewProtos) model
