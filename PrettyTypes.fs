module Starling.Pretty.Types

open Starling.Utils

/// Type of pretty-printer commands.

type Command =
    | Header of heading: string * Command
    | Separator
    | String of string
    | Surround of left: Command * mid: Command * right: Command
    | Indent of Command
    | VSep of cmds: Command list * separator: Command
    | HSep of cmds: Command list * separator: Command
    | Nop

let vsep xs = VSep (xs, Nop)
let hsep xs = HSep (xs, Nop)
let hsepStr s c = HSep (c, String s)
let commaSep = hsepStr ","
let semiSep = hsepStr ";"

let equals = String "="
let equality a b = hsep [a
                         String "="
                         b]

let ivsep = vsep >> Indent

let headed name cmds =
    VSep (cmds, Nop)
    |> Indent
    |> (curry Header) name

let keyMap =
    List.map (fun (k, v) -> HSep ( [ String k
                                     v ],
                                   (String ":")))
    >> vsep

let ssurround left right mid = Surround ((String left),
                                         mid,
                                         (String right))

let braced = ssurround "{" "}"
let angled = ssurround "<" ">"
let parened = ssurround "(" ")"
let squared = ssurround "[" "]"

/// Creates a string of spaces up to the given indent level.
let indent level = new string (' ', level * 4)

/// Enters a new line at the given indent level.
let lnIndent level = "\n" + indent level

let rec printLevel level cmd =
    match cmd with
    | Header (heading, incmd) ->
        heading + ":" + lnIndent level + printLevel level incmd
                      + lnIndent level
    | Separator ->
        "----" + lnIndent level
    | String s -> s.Replace ("\n", lnIndent level)
    | Surround (left, (VSep (cmds, _) as mid), right) ->
        printLevel level left
        + lnIndent level
        + printLevel level mid
        + lnIndent level
        + printLevel level right
    | Surround (left, mid, right) ->
        printLevel level left
        + printLevel level mid
        + printLevel level right
    | Indent incmd -> indent 1 + printLevel (level + 1) incmd
    | VSep (cmds, separator) ->
        List.map (printLevel level) cmds
        |> String.concat (printLevel level separator + lnIndent level)
    | HSep (cmds, separator) ->
        List.map (printLevel level) cmds
        |> String.concat (printLevel level separator + " ")
    | Nop -> ""

let print = printLevel 0
