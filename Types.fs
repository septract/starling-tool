namespace Starling

[<AutoOpen>]
module Types =
    type View =
        | Apply of View * args: string list
        | NamedView of string
        | Unit
        | Join of View * View

    type Command =
        | Atomic of string
        | Skip
        | Seq of Command * Command
        | Choice of Command * Command
        | Par of Command * Command
        | Star of Command
        | Viewed of ViewedCommand
    and ViewedCommand =
        | PreViewCommand of View * Command
        | PostViewCommand of Command * View
        | BothViewCommand of View * Command * View

    type Method = {
        Name   : string
        Params : string list
        Body   : Command
    }
