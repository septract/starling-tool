/// <summary>
///    The abstract syntax tree for the Starling language.
/// </summary>
module Starling.Lang.AST

open Starling
open Starling.Collections
open Starling.Core.Model
open Starling.Core.Var.Types

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
    type BopTypes =
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
    type ExpressionTypes =
        | True // true
        | False // false
        | Int of int64 // 42
        | LV of LValue // foobaz
        | Symbolic of string * Expression list // %{foo}(exprs)
        | Bop of BopTypes * Expression * Expression // a BOP b
    and Expression = Node<ExpressionTypes>

    /// An atomic action.  
    type AtomicTypes =
        | CompareAndSwap of LValue * LValue * Expression // <CAS(a, b, c)>
        | Fetch of LValue * Expression * FetchMode // <a = b??>
        | Postfix of LValue * FetchMode // <a++> or <a-->
        | Id // <id>
        | Assume of Expression // <assume(e)
    and Atomic = Node<AtomicTypes>

    /// A view prototype.
    type ViewProto = Func<Param>

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
    type CommandTypes<'view> =
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
    and Command<'view> = Node<CommandTypes<'view>>

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
    type ScriptItems =
        | Global of VarDecl // global int name;
        | Local of VarDecl // local int name;
        | Method of CMethod<Marked<View>> // method main(argv, argc) { ... }
        | Search of int // search 0;
        | ViewProto of ViewProto // view name(int arg);
        | Constraint of ViewDef<DView, Expression> // constraint emp => true
        override this.ToString() = sprintf "%A" this
    and ScriptItem = Node<ScriptItems>

/// <summary>
///     Pretty printers for the AST.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Var.Pretty

    /// Some ANSI color codes for nice outputting
    /// wraps x as <[line n: x]> with color formats
    (*
    let line_info_fmt x = sprintf "\u001b[92m<[line %d: \u001b[0m" x
    let linecol_info_fmt x y = sprintf "\u001b[92m<[line %d, \u001b[36mcol %d: \u001b[0m" x y
    let line_info f (x: Node<'a>) = hsep [ line_info_fmt x.Position.Line |> String; f x.Node; "\u001b[92m]>\u001b[0m" |> String ]
    let linecol_info f (x: Node<'a>) = hsep [ linecol_info_fmt x.Position.Line x.Position.Column |> String; f x.Node; "\u001b[92m]>\u001b[0m" |> String ]
    *)
    // reset
    let line_info f (x: Node<'a>) = f x.Node
    let linecol_info f (x: Node<'a>) = f x.Node

    /// Pretty-prints lvalues.
    let rec printLValue = function
        | LVIdent i -> String i

    /// Pretty-prints Boolean operations.
    let printBop =
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
        >> String

    /// Pretty-prints expressions.
    /// This is not guaranteed to produce an optimal expression.
    let rec printExpressions =
        function
        | True -> String "true"
        | False -> String "false"
        | Int i -> i.ToString() |> String
        | LV x -> printLValue x
        | Symbolic (sym, args) ->
            func (sprintf "%%{%s}" sym) (Seq.map printExpression args)
        | Bop(op, a, b) ->
            hsep [ printExpression a
                   printBop op
                   printExpression b ]
            |> parened
    and printExpression = linecol_info printExpressions

    /// Pretty-prints views.
    let rec printView =
        function
        | View.Func f -> printFunc printExpression f
        | View.Unit -> String "emp"
        | View.Join(l, r) -> binop "*" (printView l) (printView r)
        | View.If(e, l, r) ->
            hsep [ String "if"
                   printExpression e
                   String "then"
                   printView l
                   String "else"
                   printView r ]

    /// Pretty-prints marked view lines.
    let rec printMarkedView pView =
        function
        | Unmarked v -> pView v
        | Questioned v -> hjoin [ pView v ; String "?" ]
        | Unknown -> String "?"
        >> ssurround "{|" "|}"

    /// Pretty-prints view definitions.
    let rec printDView =
        function
        | DView.Func f -> printFunc String f
        | DView.Unit -> String "emp"
        | DView.Join(l, r) -> binop "*" (printDView l) (printDView r)

    /// Pretty-prints constraints.
    let printConstraint (cs : ViewDef<DView, Expression>) =
        hsep [ String "constraint"
               printDView (viewOf cs)
               String "->"
               (match cs with
                | Definite (_, d) -> printExpression d
                | Indefinite _ -> String "?") ]
        |> withSemi

    /// Pretty-prints fetch modes.
    let printFetchMode =
        function
        | Direct -> Nop
        | Increment -> String "++"
        | Decrement -> String "--"

    /// Pretty-prints local assignments.
    let printAssign dest src =
        equality (printLValue dest) (printExpression src)

    /// Pretty-prints atomic actions.
    let printAtomics =
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
    let printAtomic = linecol_info printAtomics

    /// Pretty-prints viewed commands with the given indent level (in spaces).
    let printViewedCommand (pView : 'view -> Command)
                           (pCmd : 'cmd -> Command)
                           ({ Command = c; Post = p } : ViewedCommand<'view, 'cmd>) =
        vsep [ pCmd c ; pView p ]

    /// Pretty-prints blocks with the given indent level (in spaces).
    let printBlock (pView : 'view -> Command)
                   (pCmd : 'cmd -> Command)
                   ({ Pre = p; Contents = c } : Block<'view, 'cmd>)
                   : Command =
        vsep ((p |> pView |> Indent)
              :: List.map (printViewedCommand pView pCmd >> Indent) c)
        |> braced

    /// Pretty-prints methods.
    let printMethod (pView : 'view -> Command)
                    (pCmd : 'cmd -> Command)
                    ({ Signature = s; Body = b } : Method<'view, 'cmd>)
                    : Command =
        hsep [ "method" |> String
               printFunc String s
               printBlock pView pCmd b ]

    /// Pretty-prints commands with the given indent level (in spaces).
    let rec printCommandTypes pView =
        function
        (* The trick here is to make Prim [] appear as ;, but
           Prim [x; y; z] appear as x; y; z;, and to do the same with
           atomic lists. *)
        | CommandTypes.Prim { PreAssigns = ps;
                 Atomics = ts;
                 PostAssigns = qs } ->
            seq { yield! Seq.map (uncurry printAssign) ps
                  yield (ts
                         |> Seq.map printAtomic
                         |> semiSep |> withSemi |> braced |> angled)
                  yield! Seq.map (uncurry printAssign) qs }
            |> semiSep |> withSemi
        | CommandTypes.If(c, t, f) ->
            hsep [ "if" |> String
                   c
                   |> printExpression
                   |> parened
                   t |> printBlock pView (printCommand pView)
                   f |> printBlock pView (printCommand pView)]
        | CommandTypes.While(c, b) ->
            hsep [ "while" |> String
                   c
                   |> printExpression
                   |> parened
                   b |> printBlock pView (printCommand pView) ]
        | CommandTypes.DoWhile(b, c) ->
            hsep [ "do" |> String
                   b |> printBlock pView (printCommand pView)
                   "while" |> String
                   c
                   |> printExpression
                   |> parened ]
            |> withSemi
        | CommandTypes.Blocks bs ->
            bs
            |> List.map (printBlock pView (printCommand pView))
            |> hsepStr "||"
    and printCommand pView = line_info (printCommandTypes pView)

    /// Pretty-prints a view prototype.
    let printViewProto { Name = n; Params = ps } =
        hsep [ "view" |> String
               func n (List.map (printCTyped String) ps) ]
        |> withSemi

    /// Pretty-prints a search directive.
    let printSearch i =
        hsep [ String "search"
               sprintf "%d" i |> String ]

    /// Pretty-prints a script variable of the given class.
    let printScriptVar cls v =
        hsep [ String cls; printCTyped String v ] |> withSemi

    /// Pretty-prints script lines.
    let printScriptLines =
        function
        | Global v -> printScriptVar "shared" v
        | Local v -> printScriptVar "thread" v
        | Method m -> printMethod (printMarkedView printView)
                                  (printCommand (printMarkedView printView)) m
        | ViewProto v -> printViewProto v
        | Search i -> printSearch i
        | Constraint c -> printConstraint c
    let printScriptLine = line_info printScriptLines

    /// Pretty-prints scripts.
    let printScript = List.map printScriptLine >> fun ls -> VSep(ls, vsep [ Nop; Nop ])


(*
 * Expression classification
 *)

/// Active pattern classifying bops as to whether they create
/// arithmetic or Boolean expressions.
let (|ArithOp|BoolOp|) =
    function
    | Mul | Div | Add | Sub -> ArithOp
    | Gt | Ge | Le | Lt -> BoolOp
    | Eq | Neq -> BoolOp
    | And | Or -> BoolOp

/// Active pattern classifying bops as to whether they take in
/// arithmetic, Boolean, or indeterminate operands.
let (|ArithIn|BoolIn|AnyIn|) =
    function
    | Mul | Div | Add | Sub -> ArithIn
    | Gt | Ge | Le | Lt -> ArithIn
    | Eq | Neq -> AnyIn
    | And | Or -> BoolIn

/// Active pattern classifying expressions as to whether they are
/// arithmetic, Boolean, or indeterminate.
let (|BoolExp|ArithExp|AnyExp|) e =
    match e.Node with
    | LV _ -> AnyExp e
    | Symbolic _ -> AnyExp e
    | Int _ -> ArithExp e
    | True | False -> BoolExp e
    | Bop(BoolOp, _, _) -> BoolExp e
    | Bop(ArithOp, _, _) -> ArithExp e

(*
 * Misc
 *)
let empty_position = { StreamName = ""; Line = 0L; Column = 0L; }
let fresh_node a = { Position = empty_position; Node = a }
let node streamname line column a = { Position = { StreamName=streamname; Line=line; Column=column }; Node = a }

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
let afunc name (pars : Expression list) : AFunc = func name pars
