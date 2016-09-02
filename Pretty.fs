/// <summary>
///     The pretty printing engine Starling uses.
/// </summary>
module Starling.Core.Pretty

open Starling.Utils
open Starling.Utils.Config


type FontColor =
    Black | Red | Green | Yellow | Blue | Magenta | Cyan | White

/// Type of pretty-printer commands.
[<NoComparison>]
type Doc =
    | Header of heading : Doc * Doc
    | Separator
    | String of string
    | Styled of style: FontColor list * cmd : Doc
    | Surround of left : Doc * mid : Doc * right : Doc
    | Indent of Doc
    | VSkip
    | VSep of cmds : Doc seq * separator : Doc
    | HSep of cmds : Doc seq * separator : Doc
    | Nop


/// Determines whether a print construct is horizontal or vertical.
let rec (|Horizontal|Vertical|) =
    function
    | (VSep(_, _) | VSkip | Separator | Header (_, _) | Surround (_, Vertical _, _) | Indent (Vertical _)) as a -> Vertical a
    | a -> Horizontal a

(*
 * Print driver
 *)

/// Creates a string of spaces up to the given indent level.
let indent level = new string(' ', level * 4)

/// Enters a new line at the given indent level.
let lnIndent level = "\n" + indent level

/// Helpers for turning a Doc into a Styled
/// for syntax highlighting keywords, literals, identifiers and view syntax
/// respectively
let syntax d = Styled([Magenta], d)
let syntaxLiteral d = Styled([Blue], d)
let syntaxIdent d = Styled([Cyan], d)
let syntaxView d = Styled([Yellow], d)

/// <summary>
///     Styles a string with ANSI escape sequences.
/// </summary>
/// <param name="s">
///     The list of styles to turn into ANSI codes and apply to the result.
/// </param>
/// <param name="d">
///     The string to stylise.
/// </param>
/// <returns>
///     The stylised (ANSI-escaped) string.
/// </param>
let stylise s d =
    let colCode =
        function
        | Black -> 0
        | Red -> 1
        | Green -> 2
        | Yellow -> 3
        | Blue -> 4
        | Magenta -> 5
        | Cyan -> 6 
        | White -> 7

    let code c = sprintf "%u" (30 + colCode c)

    let prefix = "\u001b[" + (String.concat ";" <| List.map code s) + "m"
    let suffix = "\u001b[0m"
    prefix + d + suffix

/// <summary>
///     The current state of a pretty-printer run.
/// </summary>
type PrintState =
    { /// <summary>
      ///     The current indent level of the printer.
      /// </summary>
      Level : int

      /// <summary>
      ///     Whether or not styling is to be used.
      /// </summary>
      UseStyles : bool }

/// <summary>
///     The internal print function.
/// </summary>
/// <param name="state">
///     The current state of the printer.
/// </param>
/// <returns>
///     A function mapping <see cref="Doc"/>s to strings.
/// </returns>
let rec printState state =
    function
    | Header (heading, incmd) ->
        printState state heading + ":" + lnIndent state.Level + printState state incmd + lnIndent state.Level
    | Separator ->
        "----"
    | Styled (s, d) when state.UseStyles ->
        stylise s <| printState state d
    | Styled (s, d) ->
        printState state d
    | VSkip ->
        lnIndent state.Level
    | String s ->
        s.Replace("\n", lnIndent state.Level)
    | Surround (left, Vertical mid, right) ->
        printState state left + lnIndent state.Level + printState state mid + lnIndent state.Level + printState state right
    | Surround (left, mid, right) ->
        printState state left + printState state mid + printState state right
    | Indent incmd ->
        let state' = { state with Level = state.Level + 1 }
        indent 1 + printState state' incmd
    | VSep (cmds, separator) ->
        Seq.map (printState state) cmds |> String.concat (printState state separator + lnIndent state.Level)
    | HSep (cmds, separator) ->
        Seq.map (printState state) cmds |> String.concat (printState state separator)
    | Nop -> ""

/// <summary>
///     Prints a <see cref="Doc"/> with full styling.
/// </summary>
let printStyled = printState { Level = 0; UseStyles = true }

/// <summary>
///     Prints a <see cref="Doc"/> with no styling.
/// </summary>
let printUnstyled = printState { Level = 0; UseStyles = false }


/// <summary>
///     Prints a <see cref="Doc"/>.
/// </summary>
let print = if config().color then printStyled else printUnstyled


(*
 * Shortcuts
 *)


// Hacky merge between two VSep sequences 
let vmerge a b = 
  let rec interleave = function //same as: let rec interleave (xs, ys) = match xs, ys with
    |([], ys) -> ys
    |(xs, []) -> xs
    |(x::xs, y::ys) -> x :: y :: interleave (xs,ys)

  match a, b with 
    | (VSep (xs, i), VSep (ys, j))  -> 
           let xy = interleave (List.ofSeq xs, List.ofSeq ys) in 
           VSep (Seq.ofList xy, Nop)
    | _ -> Nop


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

let cmdHeaded header cmds =
    ivsep cmds |> (curry Header) header

let headed name = cmdHeaded (String name)

let ssurround left right mid = Surround((String left), mid, (String right))
let braced = ssurround "{" "}"
let angled = ssurround "<" ">"
let parened = ssurround "(" ")"
let squared = ssurround "[" "]"

/// Pretty-prints a function f(xs1, xs2, ...xsn)
let func f xs = hjoin [String f |> syntaxIdent; commaSep xs |> parened]

/// <summary>
///    Whether to separate keys and values by colons, or by indentation.
/// </summary>
type MapSep =
    | Inline
    | Indented

/// <summary>
///     Pretty-prints an association list of Commands.
/// </summary>
/// <param name="mapSep">
///     The <c>MapSep</c> to use when joining the key and value.
/// </param>
/// <param name="_arg1">
///     An association list, as a sequence, to print.
/// </param>
/// <returns>
///     A printer for the given association list.
/// </returns>
let printAssoc mapSep =
    Seq.map
        (fun (k, v) ->
             match mapSep with
             | Inline -> colonSep [ k; v ]
             | Indented -> cmdHeaded k [ v ])
    >> vsep

/// <summary>
///     Pretty-prints a map, given printers for keys and values.
/// </summary>
/// <param name="mapSep">
///     The <c>MapSep</c> to use when joining the key and value.
/// </param>
/// <param name="pK">
///     A printer for keys.
/// </param>
/// <param name="pV">
///     A printer for values.
/// </param>
/// <param name="_arg1">
///     A map to print using <paramref name="pK" /> and <paramref name="pV" />.
/// </param>
/// <returns>
///     A printer for the given map.
/// </returns>
let printMap mapSep pK pV =
    Map.toSeq >> Seq.map (pairMap pK pV) >> printAssoc mapSep

/// Pretty-prints a list
let printList pItem lst =
    hsep [String "["; hsepStr ", " (List.map pItem lst); String "]"]

/// Formats an error that is wrapping another error.
let wrapped wholeDesc whole err =
    headed (sprintf "In %s '%s'" wholeDesc (print whole)) [ err ]
