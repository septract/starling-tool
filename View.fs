/// <summary>
///   View types
/// </summary>
module Starling.Core.View

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Traversal


/// <summary>
///     View types.
/// </summary>
[<AutoOpen>]
module Types =
    (*
     * Funcs (other than Starling.Collections.Func)
     *)

    /// A func over expressions, used in view expressions.
    type VFunc<'var> when 'var : equality = Func<Expr<'var>>

    /// A func over expressions, used in view expressions.
    type ExprFunc<'var> when 'var : equality = Func<Expr<'var>>

    /// A func over marked-var expressions.
    type MVFunc = ExprFunc<MarkedVar>

    /// A view-definition func.
    type DFunc = Func<TypedVar>

    /// A func over symbolic var expressions.
    type SVFunc = ExprFunc<Sym<Var>>

    /// A func over symbolic-marked-var expressions.
    type SMVFunc = ExprFunc<Sym<MarkedVar>>

    /// <summary>
    ///     A wrapper over funcs that adds an iterator.
    /// </summary>
    /// <typeparam name="Func">The type of wrapped funcs.</typeparam>
    /// <typeparam name="Iterator">The type of the iterator.</typeparam>
    type IteratedContainer<'Func, 'Iterator> =
        { Func : 'Func; Iterator : 'Iterator }
        override this.ToString () =
            sprintf "iter[%A](%A)" this.Iterator this.Func

    /// <summary>
    ///     Constructs an iterated container.
    /// </summary>
    /// <param name="f">The func to iterate.</param>
    /// <param name="it">The iterator to use.</param>
    /// <typeparam name="Func">The type of func to iterate.</typeparam>
    /// <typeparam name="Iterator type of iterator to use.</typeparam>
    /// <returns>
    ///     The <see cref="IteratedContainer"/> iterating over
    ///     <paramref name="f"/> <paramref name="it"/> times.
    /// </returns>
    let iterated (f : 'Func) (it : 'Iterator)
      : IteratedContainer<'Func, 'Iterator> =
        { Func = f; Iterator = it }

    /// <summary>
    ///     Maps over the func inside an iterated container.
    /// </summary>
    /// <param name="f">The mapping function to use.</param>
    /// <typeparam name="FuncA">The type of func before the map.</typeparam>
    /// <typeparam name="FuncB">The type of func after the map.</typeparam>
    /// <typeparam name="Iterator">The type of iterator.</typeparam>
    /// <returns>
    ///     A function mapping <paramref name="f"/> over the func of an
    ///     <see cref="IteratedContainer"/>.
    // </returns>
    let mapIterated (f : 'FuncA -> 'FuncB)
      ({ Func = v; Iterator = i } : IteratedContainer<'FuncA, 'Iterator>)
      : IteratedContainer<'FuncB, 'Iterator> =
        { Func = f v; Iterator = i }

    /// <summary>
    ///     Maps over the iterator an iterated container.
    /// </summary>
    /// <param name="f">The mapping function to use.</param>
    /// <typeparam name="Func">The type of func.</typeparam>
    /// <typeparam name="IterA">The iterator type before the map.</typeparam>
    /// <typeparam name="IterB">The iterator type after the map.</typeparam>
    /// <returns>
    ///     A function mapping <paramref name="f"/> over the iterator of an
    ///     <see cref="IteratedContainer"/>.
    // </returns>
    let mapIterator (f : 'IterA -> 'IterB)
      ({ Func = v; Iterator = i } : IteratedContainer<'Func, 'IterA>)
      : IteratedContainer<'Func, 'IterB> =
        { Func = v; Iterator = f i }

    /// An iterated view-definition func.
    type IteratedDFunc = IteratedContainer<DFunc, TypedVar option>

    /// <summary>
    ///     Maps a substitution function over all of the uses of an iterator
    ///     variable in a view definition.
    /// </summary>
    /// <param name="f">
    ///     The function used to substitute expressions for instances of the
    ///     iterator.
    /// </param>
    /// <param name="iterator">The variable representing the iterator.</param>
    /// <param name="defn">The view definition to transform.</param>
    /// <returns>
    ///     The result of transforming every occurrence of the integer variable
    ///     <paramref name="iterator"/> using <paramref name="f"/>.
    /// </returns>
    let mapOverIteratorUses (f : Var -> IntExpr<Sym<Var>>)
      (iterator : Var)
      (defn : BoolExpr<Sym<Var>>)
      : Result<BoolExpr<Sym<Var>>, TraversalError<'Error>> =
        let fOnIter (var : TypedVar) : Result<Expr<Sym<Var>>, 'Error> =
            ok
                (match var with
                 | Int (t, v) when v = iterator -> Int (t, f v)
                 | tv -> mkVarExp (mapCTyped Reg tv))

        let mapper =
            liftWithoutContext
                fOnIter
                (tliftToTypedSymVarSrc >> tliftToBoolSrc)

        mapper (mkTypedSub normalRec defn)

    (*
     * Views
     *)

    /// A view definition.
    type DView = IteratedDFunc list
    // TODO(CaptainHayashi): rename DView?

    /// An iterated non-D func.
    type IteratedFunc<'Var> when 'Var : equality =
        // TODO(CaptainHayashi): sort out this type mess.
        IteratedContainer<Func<Expr<'Var>>, IntExpr<'Var>>

    /// <summary>
    ///     Construct an iterated func.
    /// </summary>
    /// <param name="name">The name of the iterated func.</param>
    /// <param name="pars">The parameters of the iterated func.</param>
    /// <param name="iterator">The iterator of the iterated func.</param>
    /// <typeparam name="Var">The type of variables in the func.</typeparam>
    /// <returns>
    ///     An <see cref="IteratedFunc"/> with the given parameters.
    /// </returns>
    let iteratedFunc
      (name : string) (pars : Expr<'Var> seq) (iterator : IntExpr<'Var>)
      : IteratedFunc<'Var> =
      iterated (func name pars) iterator

    /// <summary>
    ///     A basic view, as an ordered list of VFuncs.
    /// </summary>
    type IteratedOView = IteratedFunc<Sym<MarkedVar>> list

    /// <summary>
    ///     A basic view, as an ordered list of VFuncs.
    /// </summary>
    type OView = SMVFunc list

    /// <summary>
    ///     A view expression, combining a view with its kind.
    /// </summary>
    /// <typeparam name="view">
    ///     The type of view wrapped inside this expression.
    /// </typeparam>
    type ViewExpr<'view> =
        /// <summary>
        ///     This view expression must be exercised by any proofs generated
        ///     by Starling.
        /// </summary>
        | Mandatory of 'view
        /// <summary>
        ///     This view expression may be elided in any proofs generated by
        ///     Starling.
        /// </summary>
        | Advisory of 'view


/// <summary>
///     Pretty printers for the model.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Collections.Func.Pretty
    open Starling.Collections.Multiset.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Symbolic.Pretty

    /// Pretty-prints a VFunc.
    let printVFunc pVar = printFunc (printExpr pVar)

    /// Pretty-prints an MVFunc.
    let printMVFunc = printFunc printMExpr

    /// Pretty-prints a SVFunc.
    let printSVFunc = printFunc printSVExpr

    /// Pretty-prints a SMVFunc.
    let printSMVFunc = printFunc printSMExpr

    /// Pretty-prints a DFunc.
    let printDFunc = printFunc printTypedVar

    /// Pretty-prints a View.
    let printView pVar = printMultiset (printVFunc pVar)

    /// Pretty-prints a MView.
    let printMView = printMultiset printMVFunc

    /// Prints an IteratedContainer.
    /// Iterator is suppressed if its pretty-printer returns a Nop.
    let printIteratedContainer (pFunc : 'Func -> Doc)
      (pIterator : 'Iterator -> Doc)
      ({ Iterator = i; Func = func } : IteratedContainer<'Func, 'Iterator>)
      : Doc =
        match (pIterator i) with
        | Nop -> pFunc func
        | it ->
            hjoin [ String "iter["; it; String "]"; pFunc func ]

    /// Pretty-prints an expression iterator.
    /// Yields Nop if the expression evaluates to 1.
    let printExprIterator (pVar : 'Var -> Doc)
      : IntExpr<'Var> -> Doc =
        function
        | IInt 1L -> Nop
        | e -> printIntExpr pVar e

    /// Pretty-prints an IteratedDFunc.
    let printIteratedDFunc : IteratedDFunc -> Doc =
        printIteratedContainer printDFunc (maybe Nop printTypedVar)

    /// Pretty-prints an IteratedOView.
    let printIteratedOView : IteratedOView -> Doc =
        List.map
            (printIteratedContainer
                 printSMVFunc
                 (printExprIterator (printSym printMarkedVar)))
        >> semiSep
        >> squared

    let printOView : OView -> Doc =
        List.map printSMVFunc
        >> semiSep
        >> squared

    /// Pretty-prints a DView.
    let printDView : DView -> Doc =
        List.map (printIteratedContainer printDFunc (maybe Nop printTypedVar))
        >> semiSep >> squared

    /// Pretty-prints view expressions.
    let rec printViewExpr pView =
        function
        | Mandatory v -> pView v
        | Advisory v -> hjoin [ pView v ; String "?" ]

    /// Pretty-prints model variables.
    let printModelVar (name, ty) =
        colonSep [ String name
                   printType ty ]

    /// <summary>
    ///     Pretty-prints an uninterpreted symbol.
    /// </summary>
    /// <param name="s">
    ///     The value of the symbol.
    /// </param>
    /// <returns>
    ///     A command printing <c>%{s}</c>.
    /// </returns>
    let printSymbol s =
        hjoin [ String "%" ; s |> String |> braced ]


/// <summary>
///     Type-constrained version of <c>func</c> for <c>DFunc</c>s.
/// </summary>
/// <parameter name="name">
///     The name of the <c>DFunc</c>.
/// </parameter>
/// <parameter name="pars">
///     The parameters of the <c>DFunc</c>, as a sequence.
/// </parameter>
/// <returns>
///     A new <c>DFunc</c> with the given name and parameters.
/// </returns>
let dfunc name (pars : TypedVar seq) : DFunc = func name pars

/// <summary>
///     Type-constrained version of <c>func</c> for <c>VFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>VFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>VFunc</c>, as a sequence.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>VFunc</c>'s parameters.
/// </typeparam>
/// <returns>
///     A new <c>VFunc</c> with the given name and parameters.
/// </returns>
let vfunc name (pars : Expr<'var> seq) : VFunc<'var> = func name pars

/// <summary>
///     Type-constrained version of <c>vfunc</c> for <c>MVFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>MVFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>MVFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>MVFunc</c> with the given name and parameters.
/// </returns>
let mvfunc name (pars : MExpr seq) : MVFunc = vfunc name pars

/// <summary>
///     Type-constrained version of <c>vfunc</c> for <c>SVFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>SVFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>SVFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>SVFunc</c> with the given name and parameters.
/// </returns>
let svfunc name (pars : SVExpr seq) : SVFunc = vfunc name pars


/// <summary>
///     Type-constrained version of <c>vfunc</c> for <c>SMVFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>SMVFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>SMVFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>SMVFunc</c> with the given name and parameters.
/// </returns>
let smvfunc name (pars : SMExpr seq) : SMVFunc = vfunc name pars

/// <summary>
///     Active pattern extracting a View from a ViewExpr.
/// </summary>
let ofView =
    function
    | Advisory v | Mandatory v -> v

let (|InnerView|) = ofView

/// <summary>
///     Returns true if a <c>ViewExpr</c> can be removed at will without
///     invalidating the proof.
/// </summary>
/// <param name="_arg1">
///     The <c>ViewExpr</c> to query.
/// </param>
/// <returns>
///     True if <paramref name="_arg1" /> is <c>Advisory</c> or
///     <c>Unknown</c>.
/// </returns>
let isAdvisory =
    function
    | Advisory _ -> true
    | Mandatory _ -> false


/// <summary>
///     Functions for traversing over views and funcs.
/// </summary>
module Traversal =
    open Starling.Core.Traversal

    /// <summary>
    ///   Lifts a <c>Traversal</c> over all parameters in a func.
    /// </summary>
    /// <param name="traversal">
    ///   The <c>Traversal</c> to map over all parameters in the func.
    /// </param>
    /// <typeparam name="SrcPar">
    ///     The type of parameters before traversal.
    /// </typeparam>
    /// <typeparam name="DstPar">
    ///     The type of parameters after traversal.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverFunc
      (traversal : Traversal<'SrcPar, 'DstPar, 'Error, 'Var>)
      : Traversal<Func<'SrcPar>, Func<'DstPar>, 'Error, 'Var> =
        fun context { Name = n ; Params = ps } ->
            tchainL traversal (func n) context ps
