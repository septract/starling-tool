/// <summary>
///     Module for inserting and expanding out unknown views.
/// </summary>
module Starling.Lang.ViewDesugar

open Chessie.ErrorHandling

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
///     A block whose missing views have been filled up.
/// </summary>
and FullBlock<'view, 'cmd> =
    { /// <summary> The precondition of the block.</summary>
      Pre : 'view
      /// <summary>
      ///     The commands in the block, and their subsequent views.
      /// </summary>
      Cmds : ('cmd * 'view) list }

/// <summary>A non-view command with FullBlocks.</summary>
type FullCommand' =
    /// A set of sequentially composed primitives.
    | FPrim of PrimSet
    /// An if-then-else statement, with optional else.
    | FIf of ifCond : Expression
          * thenBlock : FullBlock<ViewExpr<View>, FullCommand>
          * elseBlock : FullBlock<ViewExpr<View>, FullCommand> option
    /// A while loop.
    | FWhile of Expression * FullBlock<ViewExpr<View>, FullCommand>
    /// A do-while loop.
    | FDoWhile of FullBlock<ViewExpr<View>, FullCommand>
               * Expression // do { b } while (e)
    /// A list of parallel-composed blocks.
    | FBlocks of FullBlock<ViewExpr<View>, FullCommand> list
and FullCommand = Node<FullCommand'>

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

module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.View.Pretty
    open Starling.Lang.AST.Pretty

    /// <summary>
    ///     Prints a <see cref="FullCommand'"/>.
    /// </summary>
    /// <param name="pView">Pretty-printer for views.</param>
    /// <param name="pCmd">Pretty-printer for commands.</param>
    /// <param name="fb">The <see cref="FullBlock'"/> to print.</param>
    /// <typeparam name="View">Type of views in the block.</typeparam>
    /// <typeparam name="Cmd">Type of commands in the block.</typeparam>
    /// <returns>
    ///     The <see cref="Doc"/> representing <paramref name="fc"/>.
    /// </returns>
    let printFullBlock (pView : 'View -> Doc) (pCmd : 'Cmd -> Doc)
      (fb : FullBlock<'View, 'Cmd>) : Doc =
        let printStep (c, v) = vsep [ Indent (pCmd c); pView v ]
        let indocs = pView fb.Pre :: List.map printStep fb.Cmds
        braced (ivsep indocs)

    /// <summary>
    ///     Prints a <see cref="FullCommand'"/>.
    /// </summary>
    /// <param name="fc">The <see cref="FullCommand'"/> to print.</param>
    /// <returns>
    ///     The <see cref="Doc"/> representing <paramref name="fc"/>.
    /// </returns>
    let rec printFullCommand' (fc : FullCommand') : Doc =
        // TODO(CaptainHayashi): dedupe with PrintCommand'.
        match fc with
        (* The trick here is to make Prim [] appear as ;, but
           Prim [x; y; z] appear as x; y; z;, and to do the same with
           atomic lists. *)
        | FPrim { PreAssigns = ps; Atomics = ts; PostAssigns = qs } ->
            seq { yield! Seq.map (uncurry printAssign) ps
                  yield (ts
                         |> Seq.map printAtomic
                         |> semiSep |> withSemi |> braced |> angled)
                  yield! Seq.map (uncurry printAssign) qs }
            |> semiSep |> withSemi
        | FIf(c, t, fo) ->
            hsep [ "if" |> String |> syntax
                   c |> printExpression |> parened
                   t |> printFullBlock (printViewExpr printView) printFullCommand
                   (maybe Nop
                        (fun f ->
                            hsep
                                [ "else" |> String |> syntax
                                  printFullBlock (printViewExpr printView) printFullCommand f ])
                        fo) ]
        | FWhile(c, b) ->
            hsep [ "while" |> String |> syntax
                   parened (printExpression c)
                   b |> printFullBlock (printViewExpr printView) printFullCommand ]
        | FDoWhile(b, c) ->
            hsep [ "do" |> String |> syntax
                   printFullBlock (printViewExpr printView) printFullCommand b
                   "while" |> String |> syntax
                   parened (printExpression c) ]
            |> withSemi
        | FBlocks bs ->
            bs
            |> List.map (printFullBlock (printViewExpr printView) printFullCommand)
            |> hsepStr "||"
    /// <summary>
    ///     Prints a <see cref="FullCommand"/>.
    /// </summary>
    /// <param name="fc">The <see cref="FullCommand"/> to print.</param>
    /// <returns>
    ///     The <see cref="Doc"/> representing <paramref name="fc"/>.
    /// </returns>
    and printFullCommand (fc : FullCommand) : Doc = printFullCommand' fc.Node


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
  (cmd : Command)
    : FullCommand * DesugaredViewProto seq =
    let f = fun (a, b) -> (cmd |=> a, b)
    f <| match cmd.Node with
            | ViewExpr v -> failwith "should have been handled at block level"
            | If (e, t, fo) ->
                let t', tv = desugarBlock tvars fg t
                let f', fv =
                    match fo with
                    | None -> None, Seq.empty
                    | Some f -> f |> desugarBlock tvars fg |> pairMap Some id
                let ast = FIf (e, t', f')
                (ast, Seq.append tv fv)
            | While (e, b) ->
                let b', bv = desugarBlock tvars fg b
                (FWhile (e, b'), bv)
            | DoWhile (b, e) ->
                let b', bv = desugarBlock tvars fg b
                (FDoWhile (b', e), bv)
            | Blocks bs ->
                let bs', bsvs =
                    bs
                    |> List.map (desugarBlock tvars fg)
                    |> List.unzip
                (FBlocks bs', Seq.concat bsvs)
            | Prim ps -> (FPrim ps, Seq.empty)

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
/// <param name="block">
///     The block whose views are to be converted.
/// </param>
/// <returns>
///     A pair of the desugared block and the view prototypes generated
///     inside it.
/// </returns>
and desugarBlock (tvars: Map<string, Type>) (fg: bigint ref)
  (block: Command list)
  : FullBlock<ViewExpr<View>, FullCommand>
    * DesugaredViewProto seq = 
    (* Desugaring a block happens in two stages.
       - First, we fill in every gap where a view should be, but isn't, with
         an unknown view.
       - Next, we convert the unknown views to fresh known views. *)

    // Add an Unknown view to the start of a block without one.
    let cap l =
        match l with
        | { Node = ViewExpr v } :: _ -> (l, v)
        | _ -> (freshNode (ViewExpr Unknown) :: l, Unknown)

    (* If the first item isn't a view, we have to synthesise a block
       precondition. *)
    let (blockP, pre) = cap block
    (* If the last item isn't a view, we have to synthesise a block
       postcondition.
       (TODO(CaptainHayashi): do this efficiently) *)
    let blockPQ = List.rev (fst (cap (List.rev blockP)))

    (* Next, we have to slide down the entire block pairwise.
       1. If we see ({| view |}, {| view |}), insert a skip between them.
       2. If we see (cmd, {| view |}), add it directly to the full block;
       3. If we see ({| view |}, cmd), ignore it.  Either the view is the
          precondition at the start, which is accounted for, or it was just
          added through rule 1. and can be ignored;
       3. If we see (cmd, cmd), add (cmd, {| ? |}) to the full block.
          We'll add the next command on the next pass. *)
    let blockPairs = Seq.windowed 2 blockPQ

    let skip () =
        freshNode (Prim { PreAssigns = []; Atomics = []; PostAssigns = [] })

    let fillBlock bsf pair =
        match pair with
        | [| { Node = ViewExpr x }; { Node = ViewExpr y } |] -> (skip (), x) :: bsf
        | [| cx                   ; { Node = ViewExpr y } |] -> (cx, y) :: bsf
        | [| { Node = ViewExpr x }; cx                    |] -> bsf
        | [| cx                   : _                     |] -> (cx, Unknown) :: bsf
        | _                            -> failwith "unexpected window size"

    // The above built the block backwards, so reverse it.
    let cmds = List.rev (Seq.fold fillBlock [] blockPairs)

    // Now we can desugar each view in the block contents.
    let desugarViewedCommand (cmd, post) =
        let cmd', cProtos = desugarCommand tvars fg cmd
        let post', pProtos = desugarView tvars fg post
        ((cmd', post'), Seq.append cProtos pProtos)

    let pre', pProtos = desugarView tvars fg pre
    let cmds', csProtos =
         List.unzip (List.map desugarViewedCommand cmds)

    let block' = { Pre = pre' ; Cmds = cmds' }
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
///     The methods to convert, as a map from names to bodies..
/// </param>
/// <returns>
///     A pair of desugared methods and a sequence of <c>DesugaredViewProto</c>s.
/// </returns>
let desugar
  (tvars : VarMap)
  (methods : Map<string, Command list>)
  : (Map<string, FullBlock<ViewExpr<View>, FullCommand>> * DesugaredViewProto seq) =
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
