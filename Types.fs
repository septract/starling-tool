namespace Starling

[<AutoOpen>]
module Types =
    type Expression =
        | TrueExp
        | FalseExp
        | IntExp of int64
        | IdExp of string
        | MulExp of Expression * Expression
        | DivExp of Expression * Expression
        | AddExp of Expression * Expression
        | SubExp of Expression * Expression
        | GtExp of Expression * Expression
        | GeExp of Expression * Expression
        | LeExp of Expression * Expression
        | LtExp of Expression * Expression
        | EqExp of Expression * Expression
        | NeqExp of Expression * Expression
        | AndExp of Expression * Expression
        | OrExp of Expression * Expression

    type View =
        | Apply of View * args: string list
        | NamedView of string
        | Unit
        | Join of View * View
        | IfView of Expression * View * View

    type Command =
        | Atomic of string
        | Skip
        | If of Expression * Block * Block
        | While of Expression * Block
        | DoWhile of Block * Expression
        | Blocks of Block list

    and ViewedCommand =
        {
            Command : Command
            Post    : View
        }

    and Block = {
        Pre      : View
        // Post-condition is that in the last Seq.
        Contents : ViewedCommand list
    }

    type Constraint = {
        CView       : View
        CExpression : Expression
    }

    type Method = {
        Name   : string
        Params : string list
        Body   : Block
    }

    type ScriptItem =
        | SMethod of Method
        | SConstraint of Constraint
