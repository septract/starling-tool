namespace Starling

[<AutoOpen>]
module Types =
    /// An expression.
    /// These currently cover all languages, but this may change later.
    type Expression =
        | TrueExp                             // true
        | FalseExp                            // false
        | IntExp   of int64                   // 42
        | IdExp    of string                  // foobaz
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
    type Atomic =
        | CompareAndSwap of string * Expression * Expression // <CAS(a, b, c)>
        | Fetch of string * string * FetchMode               // <a = b??>

    /// A view.
    type View =
        // TODO(CaptainHayashi): fold Apply and NamedView into one thing?
        | Apply of View * args: string list
        | NamedView of string
        | Unit
        | Join of View * View
        | IfView of Expression * View * View

    /// A statement in the command language.
    type Command =
        | Atomic  of string                     // <a := b++>;
        | Skip                                  // ;
        | If      of Expression * Block * Block // if (e) { t } { f }
        | While   of Expression * Block         // while (e) { b }
        | DoWhile of Block * Expression         // do { b } while (e)
        | Blocks  of Block list                 // { a } || { b } || { c }

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
        CView       : View
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
        | SMethod of Method         // method main(argv, argc) { ... }
        | SConstraint of Constraint // constraint emp => true
