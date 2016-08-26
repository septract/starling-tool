/// <summary>
///    The abstract syntax tree for the Starling language.
/// </summary>
module Starling.Lang.AST

open Starling
open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Model
open Starling.Core.Var.Types
open Starling.Core.View


/// <summary>
///     Types used in the AST.
/// </summary>
[<AutoOpen>]
module Types =
    type SourcePosition =
        { StreamName: string; Line: int64; Column: int64; }
        override this.ToString() = sprintf "SourcePosition { StreamName = \"%s\"; Line = %d; Column = %d; };" this.StreamName this.Line this.Column

    /// A Node in the AST which annotates the data with information about position
    //type Node<'a> = { lineno : int; Node : 'a; }
    type Node<'a> =
        { Position: SourcePosition; Node: 'a }
        static member (|>>) (n, f) = { Position = n.Position; Node = f n.Node }
        static member (|=>) (n, b) = { Position = n.Position; Node = b }
        override this.ToString() = sprintf "<%A: %A>" this.Position this.Node

    /// A Boolean operator.
    type BinOp =
        | Mul // a * b
        | Div // a / b
        | Add // a + b
        | Sub // a - b
        | Gt // a > b
        | Ge // a >= b
        | Le // a < b
        | Lt // a <= b
        | Eq // a == b
        | Neq // a != b
        | And // a && b
        | Or // a || b

    /// An untyped, raw expression.
    /// These currently cover all languages, but this may change later.
    type Expression' =
        | True // true
        | False // false
        | Num of int64 // 42
        | LV of LValue // foobaz
        | Symbolic of string * Expression list // %{foo}(exprs)
        | BopExpr of BinOp * Expression * Expression // a BOP b
    and Expression = Node<Expression'>

    /// An atomic action.
    type Atomic' =
        | CompareAndSwap of LValue * LValue * Expression // <CAS(a, b, c)>
        | Fetch of LValue * Expression * FetchMode // <a = b??>
        | Postfix of LValue * FetchMode // <a++> or <a-->
        | Id // <id>
        | Assume of Expression // <assume(e)
    and Atomic = Node<Atomic'>

    /// A view prototype.
    type ViewProto = Func<TypedVar>

    /// A view as seen on the LHS of a ViewDef.
    type DView =
        | Unit
        | Join of DView * DView
        | Func of Func<string>

    /// <summary>
    ///     A view, annotated with additional syntax.
    ///
    ///     <para>
    ///         This is modelled as Starling's <c>ViewExpr</c>, which
    ///         cannot be <c>Unknown</c>.
    ///     </para>
    /// </summary>
    /// <typeparam name="view">
    ///     The type of view wrapped inside this expression.
    /// </typeparam>
    type Marked<'view> =
        /// <summary>
        ///     An unannotated view.
        /// </summary>
        | Unmarked of 'view
        /// <summary>
        ///     A ?-annotated view.
        /// </summary>
        | Questioned of 'view
        /// <summary>
        ///     An unknown view.
        /// </summary>
        | Unknown

    /// An AST func.
    type AFunc = Func<Expression>

    /// A view.
    type View =
        | Unit
        | Join of View * View
        | Func of AFunc
        | If of Expression * View * View

    /// A set of primitives.
    type PrimSet =
        { PreAssigns: (LValue * Expression) list
          Atomics: Atomic list
          PostAssigns: (LValue * Expression) list }

    /// A statement in the command language.
    type Command'<'view> =
        /// A set of sequentially composed primitives.
        | Prim of PrimSet
        /// An if-then-else statement.
        | If of Expression
              * Block<'view, Command<'view>>
              * Block<'view, Command<'view>>
        /// A while loop.
        | While of Expression
                 * Block<'view, Command<'view>>
        /// A do-while loop.
        | DoWhile of Block<'view, Command<'view>>
                   * Expression // do { b } while (e)
        /// A list of parallel-composed blocks.
        | Blocks of Block<'view, Command<'view>> list
    and Command<'view> = Node<Command'<'view>>

    /// A combination of a command and its postcondition view.
    and ViewedCommand<'view, 'cmd> =
        { Command : 'cmd // <a := b++>;
          Post : 'view } // {| a = b |}

    /// A block or method body.
    and Block<'view, 'cmd> =
        { Pre : 'view
          // Post-condition is that in the last Seq.
          Contents : ViewedCommand<'view, 'cmd> list }

    /// A method.
    type Method<'view, 'cmd> =
        { Signature : Func<string> // main (argv, argc) ...
          Body : Block<'view, 'cmd> } // ... { ... }

    /// Synonym for methods over CommandTypes.
    type CMethod<'view> = Method<'view, Command<'view>>

    /// A top-level item in a Starling script.
    type ScriptItem' =
        | Global of TypedVar // global int name;
        | Local of TypedVar // local int name;
        | Method of CMethod<Marked<View>> // method main(argv, argc) { ... }
        | Search of int // search 0;
        | ViewProto of ViewProto // view name(int arg);
        | Constraint of DView * Expression option // constraint emp => true
        override this.ToString() = sprintf "%A" this
    and ScriptItem = Node<ScriptItem'>

/// <summary>
///     Pretty printers for the AST.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Collections.Func.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Var.Pretty

    /// Pretty-prints lvalues.
    let rec printLValue : LValue -> Doc =
        function
        | LVIdent i -> String i

    /// Pretty-prints Boolean operations.
    let printBinOp : BinOp -> Doc =
        function
        | Mul -> "*"
        | Div -> "/"
        | Add -> "+"
        | Sub -> "-"
        | Gt -> ">"
        | Ge -> ">="
        | Le -> "<"
        | Lt -> "<="
        | Eq -> "=="
        | Neq -> "!="
        | And -> "&&"
        | Or -> "||"
        >> String >> syntax

    /// Pretty-prints expressions.
    /// This is not guaranteed to produce an optimal expression.
    let rec printExpression' : Expression' -> Doc =
        function
        | True -> String "true" |> syntaxLiteral
        | False -> String "false" |> syntaxLiteral
        | Num i -> i.ToString() |> String |> syntaxLiteral
        | LV x -> printLValue x
        | Symbolic (sym, args) ->
            func (sprintf "%%{%s}" sym) (Seq.map printExpression args)
        | BopExpr(op, a, b) ->
            hsep [ printExpression a
                   printBinOp op
                   printExpression b ]
            |> parened
    and printExpression (x : Expression) : Doc = printExpression' x.Node

    /// Pretty-prints views.
    let rec printView : View -> Doc =
        function
        | View.Func f -> printFunc printExpression f
        | View.Unit -> String "emp" |> syntaxView
        | View.Join(l, r) -> binop "*" (printView l) (printView r)
        | View.If(e, l, r) ->
            hsep [ String "if" |> syntaxView
                   printExpression e
                   String "then" |> syntaxView
                   printView l
                   String "else" |> syntaxView
                   printView r ]

    /// Pretty-prints marked view lines.
    let rec printMarkedView (pView : 'view -> Doc) : Marked<'view> -> Doc =
        function
        | Unmarked v -> pView v
        | Questioned v -> hjoin [ pView v ; String "?" |> syntaxView ]
        | Unknown -> String "?" |> syntaxView
        >> ssurround "{| " " |}"

    /// Pretty-prints view definitions.
    let rec printDView : DView -> Doc =
        function
        | DView.Func f -> printFunc String f
        | DView.Unit -> String "emp" |> syntaxView
        | DView.Join(l, r) -> binop "*" (printDView l) (printDView r)

    /// Pretty-prints constraints.
    let printConstraint (view : DView) (def : Expression option) : Doc =
        hsep [ String "constraint" |> syntax
               printDView view
               String "->" |> syntax
               (match def with
                | Some d -> printExpression d
                | None _ -> String "?" |> syntax) ]
        |> withSemi

    /// Pretty-prints fetch modes.
    let printFetchMode : FetchMode -> Doc =
        function
        | Direct -> Nop
        | Increment -> String "++"
        | Decrement -> String "--"

    /// Pretty-prints local assignments.
    let printAssign (dest : LValue) (src : Expression) : Doc =
        equality (printLValue dest) (printExpression src)

    /// Pretty-prints atomic actions.
    let printAtomic' : Atomic' -> Doc =
        function
        | CompareAndSwap(l, f, t) ->
            func "CAS" [ printLValue l
                         printLValue f
                         printExpression t ]
        | Fetch(l, r, m) ->
            equality (printLValue l) (hjoin [ printExpression r
                                              printFetchMode m ])
        | Postfix(l, m) ->
            hjoin [ printLValue l
                    printFetchMode m ]
        | Id -> String "id"
        | Assume e -> func "assume" [ printExpression e ]
    let printAtomic (x : Atomic) : Doc = printAtomic' x.Node

    /// Pretty-prints viewed commands with the given indent level (in spaces).
    let printViewedCommand (pView : 'view -> Doc)
                           (pCmd : 'cmd -> Doc)
                           ({ Command = c; Post = p } : ViewedCommand<'view, 'cmd>)
                           : Doc =
        vsep [ pCmd c ; pView p ]

    /// Pretty-prints blocks with the given indent level (in spaces).
    let printBlock (pView : 'view -> Doc)
                   (pCmd : 'cmd -> Doc)
                   ({ Pre = p; Contents = c } : Block<'view, 'cmd>)
                   : Doc =
        vsep ((p |> pView |> Indent)
              :: List.map (printViewedCommand pView pCmd >> Indent) c)
        |> braced

    /// Pretty-prints methods.
    let printMethod (pView : 'view -> Doc)
                    (pCmd : 'cmd -> Doc)
                    ({ Signature = s; Body = b } : Method<'view, 'cmd>)
                    : Doc =
        hsep [ "method" |> String |> syntax
               printFunc (String >> syntaxIdent) s
               printBlock pView pCmd b ]

    /// Pretty-prints commands.
    let rec printCommand' (pView : 'view -> Doc) : Command'<'view> -> Doc =
        function
        (* The trick here is to make Prim [] appear as ;, but
           Prim [x; y; z] appear as x; y; z;, and to do the same with
           atomic lists. *)
        | Command'.Prim { PreAssigns = ps; Atomics = ts; PostAssigns = qs } ->
            seq { yield! Seq.map (uncurry printAssign) ps
                  yield (ts
                         |> Seq.map printAtomic
                         |> semiSep |> withSemi |> braced |> angled)
                  yield! Seq.map (uncurry printAssign) qs }
            |> semiSep |> withSemi
        | Command'.If(c, t, f) ->
            hsep [ "if" |> String |> syntax
                   c
                   |> printExpression
                   |> parened
                   t |> printBlock pView (printCommand pView)
                   f |> printBlock pView (printCommand pView) ]
        | Command'.While(c, b) ->
            hsep [ "while" |> String |> syntax
                   c
                   |> printExpression
                   |> parened
                   b |> printBlock pView (printCommand pView) ]
        | Command'.DoWhile(b, c) ->
            hsep [ "do" |> String |> syntax
                   b |> printBlock pView (printCommand pView)
                   "while" |> String |> syntax
                   c
                   |> printExpression
                   |> parened ]
            |> withSemi
        | Command'.Blocks bs ->
            bs
            |> List.map (printBlock pView (printCommand pView))
            |> hsepStr "||"
    and printCommand (pView : 'view -> Doc)
                     (x : Command<'view>)
                     : Doc =
        printCommand' pView x.Node

    /// Pretty-prints a view prototype.
    let printViewProto ({ Name = n; Params = ps } : ViewProto) : Doc =
        hsep [ "view" |> String |> syntax
               func n (List.map (printCTyped String) ps) ]
        |> withSemi

    /// Pretty-prints a search directive.
    let printSearch (i : int) : Doc =
        hsep [ String "search" |> syntax
               sprintf "%d" i |> String ]

    /// Pretty-prints a script variable of the given class.
    let printScriptVar (cls : string) (v : CTyped<Var>) : Doc =
        hsep [ String cls |> syntax; printCTyped String v ] |> withSemi

    /// Pretty-prints script lines.
    let printScriptItem' : ScriptItem' -> Doc =
        function
        | Global v -> printScriptVar "shared" v
        | Local v -> printScriptVar "thread" v
        | Method m ->
            fun mdoc -> vsep [Nop; mdoc; Nop]
            <| printMethod (printMarkedView printView) (printCommand (printMarkedView printView)) m
        | ViewProto v -> printViewProto v
        | Search i -> printSearch i
        | Constraint (view, def) -> printConstraint view def
    let printScriptItem (x : ScriptItem) : Doc = printScriptItem' x.Node

    /// Pretty-prints scripts.
    /// each line on its own line
    let printScript (xs : ScriptItem list) : Doc =
        VSep (List.map printScriptItem xs, Nop)


(*
 * Expression classification
 *)

/// Active pattern classifying bops as to whether they create
/// arithmetic or Boolean expressions.
let (|ArithOp|BoolOp|) : BinOp -> Choice<unit, unit> =
    function
    | Mul | Div | Add | Sub -> ArithOp
    | Gt | Ge | Le | Lt -> BoolOp
    | Eq | Neq -> BoolOp
    | And | Or -> BoolOp

/// Active pattern classifying bops as to whether they take in
/// arithmetic, Boolean, or indeterminate operands.
let (|ArithIn|BoolIn|AnyIn|) : BinOp -> Choice<unit, unit, unit> =
    function
    | Mul | Div | Add | Sub -> ArithIn
    | Gt | Ge | Le | Lt -> ArithIn
    | Eq | Neq -> AnyIn
    | And | Or -> BoolIn

/// Active pattern classifying expressions as to whether they are
/// arithmetic, Boolean, or indeterminate.
let (|BoolExp|ArithExp|AnyExp|) (e : Expression)
  : Choice<Expression, Expression, Expression> =
    match e.Node with
    | LV _ -> AnyExp e
    | Symbolic _ -> AnyExp e
    | Num _ -> ArithExp e
    | True | False -> BoolExp e
    | BopExpr(BoolOp, _, _) -> BoolExp e
    | BopExpr(ArithOp, _, _) -> ArithExp e

(*
 * Misc
 *)
let emptyPosition : SourcePosition =
    { StreamName = ""; Line = 0L; Column = 0L; }
let freshNode (a : 'a) : Node<'a> =
  { Position = emptyPosition; Node = a }
let node (streamname : string)
         (line : int64)
         (column : int64)
         (a : 'a)
         : Node<'a> =
    { Position = { StreamName = streamname; Line = line; Column = column }; Node = a }

/// <summary>
///     Type-constrained version of <c>func</c> for <c>AFunc</c>s.
/// </summary>
/// <parameter name="name">
///   The name of the <c>AFunc</c>.
/// </parameter>
/// <parameter name="pars">
///   The parameters of the <c>AFunc</c>, as a sequence.
/// </parameter>
/// <returns>
///   A new <c>AFunc</c> with the given name and parameters.
/// </returns>
let afunc (name : string) (pars : Expression list) : AFunc = func name pars
