/// <summary>
///     Module for desugaring <c>{|?|}</c> views into fresh views.
/// </summary>
module Starling.Lang.ViewDesugar

open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.View
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Lang.AST

/// <summary>
///     A partly modelled view prototype, whose parameters use Starling's type
///     system rather than the language's.
/// </summary>
type DesugaredViewProto = GeneralViewProto<TypedVar>

/// <summary>
///     Generates a new view from an unknown view expression.
/// </summary>
/// <param name="tvars">
///     The environment of thread-local variables.
/// </param>
/// <param name="fg">
///     The fresh-generator used to make new views when the <c>ViewExpr</c>
///     is <c>Unknown</c>.
/// </param>
/// <returns>
///     A pair of a fresh <c>View</c>, and its corresponding <c>ViewProto</c>.
/// </returns>
let makeFreshView (tvars : VarMap) (fg : FreshGen) : View * DesugaredViewProto =
    let viewName =
        fg |> getFresh |> sprintf "%A"
    let viewArgs =
        tvars |> Map.toSeq |> Seq.map (fst >> Identifier >> fun l -> freshNode l)
    let viewParams = VarMap.toTypedVarSeq tvars

    (Func (func viewName viewArgs), NoIterator (func viewName viewParams, false))

/// <summary>
///     Converts a possibly-unknown view into a block over known views.
/// </summary>
/// <param name="tvars">
///     The <c>VarMap</c> of thread-local variables.
/// </param>
/// <param name="fg">
///     The fresh-number generator used to name the views.
/// </param>
/// <param name="_arg1">
///     The view to be converted.
/// </param>
/// <returns>
///     A pair of the desugared view and the view prototypes generated
///     inside it.
/// </returns>
let desugarView (tvars : VarMap) (fg : FreshGen)
  : Marked<View> -> ViewExpr<View> * DesugaredViewProto seq =
    function
    | Unmarked v -> (Mandatory v, Seq.empty)
    | Questioned v -> (Advisory v, Seq.empty)
    | Unknown ->
        makeFreshView tvars fg |> pairMap Advisory Seq.singleton

/// <summary>
///     Converts a command whose views can be unknown into one
///     over known views.
/// </summary>
/// <param name="tvars">
///     The <c>VarMap</c> of thread-local variables.
/// </param>
/// <param name="fg">
///     The fresh-number generator used to name the views.
/// </param>
/// <param name="_arg1">
///     The command whose views are to be converted.
/// </param>
/// <returns>
///     A pair of the desugared command and the view prototypes
///     generated inside it.
/// </returns>
let rec desugarCommand (tvars : VarMap) (fg : FreshGen)
  (cmd : Command<Marked<View>>)
    : Command<ViewExpr<View>> * DesugaredViewProto seq =
    let f = fun (a, b) -> (cmd |=> a, b)
    f <| match cmd.Node with
            | If (e, t, fo) ->
                let t', tv = desugarBlock tvars fg t
                let f', fv =
                    match fo with
                    | None -> None, Seq.empty
                    | Some f -> f |> desugarBlock tvars fg |> pairMap Some id
                let ast = If (e, t', f')
                (ast, Seq.append tv fv)
            | While (e, b) ->
                let b', bv = desugarBlock tvars fg b
                (While (e, b'), bv)
            | DoWhile (b, e) ->
                let b', bv = desugarBlock tvars fg b
                (DoWhile (b', e), bv)
            | Blocks bs ->
                let bs', bsvs =
                    bs
                    |> List.map (desugarBlock tvars fg)
                    |> List.unzip
                (Blocks bs', Seq.concat bsvs)
            | Prim ps -> (Prim ps, Seq.empty)

/// <summary>
///     Converts a viewed command whose views can be unknown into one
///     over known views.
/// </summary>
/// <param name="tvars">
///     The <c>VarMap</c> of thread-local variables.
/// </param>
/// <param name="fg">
///     The fresh-number generator used to name the views.
/// </param>
/// <param name="_arg1">
///     The viewed command whose views are to be converted.
/// </param>
/// <returns>
///     A pair of the desugared viewed command and the view prototypes
///     generated inside it.
/// </returns>
and desugarViewedCommand (tvars : VarMap) (fg : FreshGen)
  ({ Command = c ; Post = q }
     : ViewedCommand<Marked<View>, Command<Marked<View>>>)
  : ViewedCommand<ViewExpr<View>, Command<ViewExpr<View>>> * DesugaredViewProto seq =
    let c', cProtos = desugarCommand tvars fg c
    let q', qProtos = desugarView tvars fg q

    let block' = { Command = c' ; Post = q' }
    (block', Seq.append qProtos cProtos)

/// <summary>
///     Converts a block whose views can be unknown into a block over known
///     views.
/// </summary>
/// <param name="tvars">
///     The <c>VarMap</c> of thread-local variables.
/// </param>
/// <param name="fg">
///     The fresh-number generator used to name the views.
/// </param>
/// <param name="_arg1">
///     The block whose views are to be converted.
/// </param>
/// <returns>
///     A pair of the desugared block and the view prototypes generated
///     inside it.
/// </returns>
and desugarBlock (tvars: Map<string, Type>) (fg: bigint ref) (blk: Block<Marked<View>, Command<Marked<View>>>)
    : Block<ViewExpr<View>, Command<ViewExpr<View>>> * DesugaredViewProto seq =
    let p, cs = blk.Pre, blk.Contents
    let p', pProtos = desugarView tvars fg p
    let cs', csProtos =
        cs
        |> List.map (desugarViewedCommand tvars fg)
        |> List.unzip

    let block' = { Pre = p' ; Contents = cs' }
    let res = (block', Seq.concat (pProtos :: csProtos))
    res

/// <summary>
///     Converts a sequence of methods whose views can be unknown into
///     a sequence of methods over known views.
///
///     <para>
///         This effectively replaces every view <c>{| ? |}</c> with
///         a view <c>{| n(locals) |}</c>, where <c>n</c> is fresh,
///         and then adds <c>n</c> to the view prototypes considered by
///         the constraint searcher.
///     </para>
/// </summary>
/// <param name="tvars">
///     The <c>VarMap</c> of thread-local variables.
/// </param>
/// <param name="methods">
///     The methods to convert, as a map from names to bodies..
/// </param>
/// <returns>
///     A pair of desugared methods and a sequence of <c>DesugaredViewProto</c>s.
/// </returns>
let desugar
  (tvars : VarMap)
  (methods : Map<string, Block<Marked<View>, Command<Marked<View>>>>)
  : (Map<string, Block<ViewExpr<View>, Command<ViewExpr<View>>>> * DesugaredViewProto seq) =
    let fg = freshGen ()
    let desugaredSeq =
        Seq.map
            (fun (n, b) ->
                 let b', vsNew = desugarBlock tvars fg b
                 ((n, b'), vsNew))
            (Map.toSeq methods)
    let methods', vprotoSeqs = List.unzip (Seq.toList desugaredSeq)
    (Map.ofSeq methods', Seq.concat vprotoSeqs)


/// <summary>
///     Tests for <c>ViewDesugar</c>.
/// </summary>
module Tests =
    open NUnit.Framework

    /// <summary>
    ///     NUnit tests for <c>ViewDesugar</c>.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for <c>desugarView</c>.
        /// </summary>
        static member ViewDesugars =
            [TestCaseData(Unknown : Marked<View>)
              .Returns((Func
                            (func "0" [ freshNode <| Identifier "s" ; freshNode <| Identifier "t" ]),
                        Seq.singleton <| func "0" [ (Int, "s"), (Int, "t") ]))
              .SetName("Desugaring an unknown view creates a fresh view\
                        with a fresh name and all locals as parameters") ]

        /// <summary>
        ///     Tests <c>desugarView</c>.
        /// </summary>
        member x.``Marked views desugar properly into ViewExprs`` v =
             let fg = freshGen ()
             desugarView (Map.ofList [ ("s", Type.Int (normalRec, ()))
                                       ("t", Type.Int (normalRec, ())) ])
                         fg v
