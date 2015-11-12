﻿namespace Starling

module AST =
    /// An lvalue.
    /// This is given a separate type in case we add to it later.
    type LValue =
        | LVIdent of string
        | LVPtr   of LValue

    /// An untyped, raw expression.
    /// These currently cover all languages, but this may change later.
    type Expression =
        | TrueExp                             // true
        | FalseExp                            // false
        | IntExp   of int64                   // 42
        | LVExp    of LValue                  // foobaz
        | MulExp   of Expression * Expression // a * b
        | DivExp   of Expression * Expression // a / b
        | AddExp   of Expression * Expression // a + b
        | SubExp   of Expression * Expression // a - b
        | GtExp    of Expression * Expression // a > b
        | GeExp    of Expression * Expression // a >= b
        | LeExp    of Expression * Expression // a < b
        | LtExp    of Expression * Expression // a <= b
        | EqExp    of Expression * Expression // a == b
        | NeqExp   of Expression * Expression // a != b
        | AndExp   of Expression * Expression // a && b
        | OrExp    of Expression * Expression // a || b

    /// A mode for the Fetch atomic action.
    type FetchMode =
        | Direct    // <a = b>
        | Increment // <a = b++>
        | Decrement // <a = b-->

    /// An atomic action.
    type AtomicAction =
        | CompareAndSwap of LValue * Expression * Expression // <CAS(a, b, c)>
        | Fetch of LValue * LValue * FetchMode               // <a = b??>
        | Postfix of LValue * FetchMode                      // <a++> or <a-->

    /// A variable type.
    type Type =
        | Int  // int
        | Bool // bool

    /// A view prototype.
    type ViewProto =
        {
            VPName: string
            VPPars: ( Type * string ) list
        }

    /// A view definition.
    type ViewDef =
        | DUnit
        | DJoin of ViewDef * ViewDef
        | DFunc of string * pars: string list

    /// A view expression.
    type View =
        | Unit
        | Join   of View * View
        | Func   of string * args: Expression list
        | IfView of Expression * View * View

    /// A statement in the command language.
    type Command =
        | Atomic  of AtomicAction               // <a = b++>;
        | Skip                                  // ;
        | If      of Expression * Block * Block // if (e) { t } { f }
        | While   of Expression * Block         // while (e) { b }
        | DoWhile of Block * Expression         // do { b } while (e)
        | Blocks  of Block list                 // { a } || { b } || { c }
        | Assign  of LValue * Expression        // a = b;

    /// A combination of a command and its postcondition view.
    and ViewedCommand =
        {
            Command : Command // <a := b++;
            Post    : View    // {| a = b |}
        }

    /// A block or method body.
    and Block = {
        Pre      : View
        // Post-condition is that in the last Seq.
        Contents : ViewedCommand list
    }

    /// A constraint, binding a view to an expression.
    type Constraint = {
        CView       : ViewDef
        CExpression : Expression
    }

    /// A method.
    type Method = {
        Name   : string      // main ...
        Params : string list //      ... (argv, argc) ...
        Body   : Block       //                       ... { ... }
    }

    /// A top-level item in a Starling script.
    type ScriptItem =
        | SGlobal of Type * string  // global int name;
        | SLocal  of Type * string  // local int name;
        | SMethod of Method         // method main(argv, argc) { ... }
        | SViewProto of ViewProto   // view name(int arg);
        | SConstraint of Constraint // constraint emp => true