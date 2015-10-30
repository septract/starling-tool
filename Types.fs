namespace Starling

[<AutoOpen>]
module Types =
    type View =
        | Apply of View * args: string list
        | NamedView of string
        | Unit
        | Join of View * View
        | IfView of string * View * View

    type Command =
        | Atomic of string
        | Skip
        | If of string * Block * Block
        | While of string * Block
        | DoWhile of Block * string
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
        CExpression : string
    }

    type Method = {
        Name   : string
        Params : string list
        Body   : Block
    }

    type ScriptItem =
        | SMethod of Method
        | SConstraint of Constraint
