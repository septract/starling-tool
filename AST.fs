module Starling.Lang.AST

open Starling
open Starling.Collections

/// A Boolean operator.
type Bop = 
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
type Expression = 
    | True // true
    | False // false
    | Int of int64 // 42
    | LV of Var.LValue // foobaz
    | Bop of Bop * Expression * Expression // a BOP b

/// An atomic action.
type AtomicAction = 
    | CompareAndSwap of Var.LValue * Var.LValue * Expression // <CAS(a, b, c)>
    | Fetch of Var.LValue * Expression * Var.FetchMode // <a = b??>
    | Postfix of Var.LValue * Var.FetchMode // <a++> or <a-->
    | Id // <id>
    | Assume of Expression // <assume(e)

/// A view prototype.
type ViewProto = Func<(Var.Type * string)>

/// A view definition.
type ViewDef = 
    | Unit
    | Join of ViewDef * ViewDef
    | Func of Func<string>

/// A view expression.
type View = 
    | Unit
    | Join of View * View
    | Func of Func<Expression>
    | IfView of Expression * View * View

/// A statement in the command language.
type Command = 
    | Atomic of AtomicAction // <a = b++>;
    | Skip // ;
    | If of Expression * Block * Block // if (e) { t } { f }
    | While of Expression * Block // while (e) { b }
    | DoWhile of Block * Expression // do { b } while (e)
    | Blocks of Block list // { a } || { b } || { c }
    | Assign of Var.LValue * Expression // a = b;

/// A combination of a command and its postcondition view.
and ViewedCommand = 
    { Command : Command // <a := b++;
      Post : View } // {| a = b |}

/// A block or method body.
and Block = 
    { Pre : View
      // Post-condition is that in the last Seq.
      Contents : ViewedCommand list }

/// A constraint, binding a view to an expression.
type Constraint = 
    { CView : ViewDef
      CExpression : Expression }

/// A method.
type Method = 
    { Signature : Func<string> // main (argv, argc) ...
      Body : Block } // ... { ... }

/// A top-level item in a Starling script.
type ScriptItem = 
    | Global of Var.Type * string // global int name;
    | Local of Var.Type * string // local int name;
    | Method of Method // method main(argv, argc) { ... }
    | ViewProto of ViewProto // view name(int arg);
    | Constraint of Constraint // constraint emp => true
