module Starling.Pretty.Types

open Starling.Collections
open Starling.Utils

/// Type of pretty-printer commands.
[<NoComparison>]
type Command = 
    | Header of heading : string * Command
    | Separator
    | String of string
    | Surround of left : Command * mid : Command * right : Command
    | Indent of Command
    | VSkip
    | VSep of cmds : Command seq * separator : Command
    | HSep of cmds : Command seq * separator : Command
    | Nop

(*
 * Print driver
 *)

/// Creates a string of spaces up to the given indent level.
let indent level = new string(' ', level * 4)

/// Enters a new line at the given indent level.
let lnIndent level = "\n" + indent level

let rec printLevel level = 
    function 
    | Header(heading, incmd) -> heading + ":" + lnIndent level + printLevel level incmd + lnIndent level
    | Separator -> "----"
    | VSkip -> lnIndent level
    | String s -> s.Replace("\n", lnIndent level)
    | Surround(left, (VSep(_, _) as mid), right) -> 
        printLevel level left + lnIndent level + printLevel level mid + lnIndent level + printLevel level right
    | Surround(left, mid, right) -> printLevel level left + printLevel level mid + printLevel level right
    | Indent incmd -> indent 1 + printLevel (level + 1) incmd
    | VSep(cmds, separator) -> 
        Seq.map (printLevel level) cmds |> String.concat (printLevel level separator + lnIndent level)
    | HSep(cmds, separator) -> Seq.map (printLevel level) cmds |> String.concat (printLevel level separator)
    | Nop -> ""

let print = printLevel 0

(*
 * Shortcuts
 *)

let fmt fstr xs =
    (* This weird casting dance is how we tell Format to use the obj[] overload.
     * Otherwise, it might try to print xss as if it's one argument!
     *)
    let xss : obj[] = xs |> Seq.map (print >> fun x -> x :> obj) |> Seq.toArray
    System.String.Format(fstr, xss) |> String
let vsep xs = VSep(xs, Nop)
let hsepStr s c = HSep(c, String s)

/// Horizontally joins a list of commands with no separator.
let hjoin c = HSep(c, Nop)
/// Horizontally separates a list of commands with a space separator.
let hsep c = hsepStr " " c
/// Horizontally separates a list of commands with commas.
let commaSep c = hsepStr ", " c
/// Horizontally separates a list of commands with semicolons.
let semiSep c = hsepStr "; " c
/// Horizontally separates a list of commands with colons.
let colonSep c = hsepStr ": " c

/// Appends a semicolon to a command.
let withSemi a = hjoin [a; String ";"]

/// The string '=' as a command.
let equals = String "="

/// A binary operation a o b, where o is a String..
let binop o a b =
    hsep [ a
           String o
           b ]

let equality = binop "="

let ivsep c = c |> vsep |> Indent

let headed name cmds = 
    ivsep cmds |> (curry Header) name

let keyMap = 
    List.map (fun (k, v) -> 
        colonSep [ String k
                   v ])
    >> vsep

let ssurround left right mid = Surround((String left), mid, (String right))
let braced = ssurround "{" "}"
let angled = ssurround "<" ">"
let parened = ssurround "(" ")"
let squared = ssurround "[" "]"

/// Pretty-prints a function f(xs1, xs2, ...xsn)
let func f xs = hjoin [String f; commaSep xs |> parened]

/// Pretty-prints Funcs using pxs to print parameters.
let printFunc pxs { Starling.Collections.Func.Name = f; Params = xs } = func f (Seq.map pxs xs)
