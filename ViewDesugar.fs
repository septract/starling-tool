/// <summary>
///     Module for desugaring <c>{|?|}</c> views into fresh views.
/// </summary>
module Starling.Lang.ViewDesugar

open Starling.Collections
open Starling.Utils
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Lang.AST


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
let makeFreshView tvars fg =
    let viewName =
        fg |> getFresh |> sprintf "%A"
    let viewArgs =
        tvars |> Map.toSeq |> Seq.map (fst >> LVIdent >> LV)
    let viewParams =
        tvars |> Map.toSeq |> Seq.map (fun (name, ty) -> withType ty name)

    (Func (func viewName viewArgs), func viewName viewParams)

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
let desugarView tvars fg =
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
let rec desugarCommand tvars fg =
    function
    | If (e, t, f) ->
        let t', tv = desugarBlock tvars fg t
        let f', fv = desugarBlock tvars fg f
        (If (e, t', f'), Seq.append tv fv)
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
and desugarViewedCommand tvars fg { Command = c ; Post = q } =
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
and desugarBlock tvars fg { Pre = p ; Contents = cs } =
    let p', pProtos = desugarView tvars fg p
    let cs', csProtos =
        cs
        |> List.map (desugarViewedCommand tvars fg)
        |> List.unzip

    let block' = { Pre = p' ; Contents = cs' }

    (block', Seq.concat (pProtos :: csProtos))

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
///     The sequence of methods to convert.
/// </param>
/// <returns>
///     A pair of desugared methods and a sequence of <c>ViewProto</c>s.
/// </returns>
let desugar tvars methods =
    let fg = freshGen ()
    let methods', vprotoSeqs =
        methods
        |> Seq.map
            (fun { Signature = s ; Body = b } ->
                 let b', vsNew = desugarBlock tvars fg b
                 let m' = { Signature = s ; Body = b' }
                 (m', vsNew))
        |> Seq.toList
        |> List.unzip
    (Seq.rev methods', Seq.concat vprotoSeqs)


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
                            (func "0" [ LV (LVIdent "s") ; LV (LVIdent "t") ]),
                        Seq.singleton <| func "0" [ (Int, "s"), (Int, "t") ]))
              .SetName("Desugaring an unknown view creates a fresh view\
                        with a fresh name and all locals as parameters") ]

        /// <summary>
        ///     Tests <c>desugarView</c>.
        /// </summary>
        member x.``Marked views desugar properly into ViewExprs`` v =
             let fg = freshGen ()
             desugarView (Map.ofList [ ("s", Type.Int ())
                                       ("t", Type.Int ()) ])
                         fg v
