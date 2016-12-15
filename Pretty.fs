/// <summary>
///     The pretty printing engine Starling uses.
/// </summary>
module Starling.Core.Pretty

open Starling.Utils
open Starling.Utils.Config


type FontColor =
    Black | Red | Green | Yellow | Blue | Magenta | Cyan | White

/// <summary>
///     Type of LaTeX commands.
/// </summary>
[<NoComparison>]
type LatexCmd<'A> =
    { /// <summary>The name of the command.</summary>
      Name : string
      /// <summary>The arguments of the command.</summary>
      Args : 'A list }

/// <summary>
///     Type of pretty-printer commands.
/// </summary>
[<NoComparison>]
type Doc =
    | Header of heading : Doc * Doc
    | Separator
    | String of string
    | Styled of style: FontColor list * cmd : Doc
    | /// <summary>
      ///    A document that should be output in typewriter font in LaTeX mode.
      /// </summary>
      Verbatim of Doc
    | /// <summary>
      ///    A document that has a separate LaTeX version.
      ///    The LaTeX version is stored as a func and emitted as a command
      ///    \name{arg}{arg}...
      /// </summary>
      Latex of latexVar : LatexCmd<Doc> * normalVar : Doc
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
let syntax d = Verbatim(Styled([Magenta], d))
let syntaxLiteral d = Verbatim(Styled([Blue], d))
let syntaxIdent d = Verbatim(Styled([Cyan], d))
let syntaxView d = Verbatim(Styled([Yellow], d))

let syntaxStr d = syntax (String d)
let syntaxLiteralStr d = syntaxLiteral (String d)
let syntaxIdentStr d = syntaxIdent (String d)
let syntaxViewStr d = syntaxView (String d)

(* Helpers for styling Docs for errors. *)
let error d = Styled([Red], d)
let errorContext d = Styled([Cyan], d)
let errorInfo d = Styled([Magenta], d)
let warning d = Styled([Yellow], d)
let success d = Styled([Green], d)
let inconclusive d = Styled([Blue], d)

let errorStr s = error (String s)
let errorInfoStr s = errorInfo (String s)

/// <summary>
///     Styles a string with LaTeX (xcolor) escape sequences.
/// </summary>
/// <param name="s">
///     The list of styles to turn into xcolor directives and apply to the result.
/// </param>
/// <param name="l">
///     The optional list of styles previously in effect (ignored).
/// </param>
/// <param name="d">
///     The string to stylise.
/// </param>
/// <returns>
///     The stylised (xcolor-annotated) string.
/// </param>
let latexStylise s l d =
    let colName =
        function
        | Black -> "black"
        | Red -> "red"
        | Green -> "green"
        | Yellow -> "yellow"
        | Blue -> "blue"
        | Magenta -> "magenta"
        | Cyan -> "cyan"
        | White -> "white"

    let rec build pre suf =
        function
        | [] -> pre + d + suf
        | x::xs -> build (sprintf "%s{\\color{%s}" pre (colName x)) ("}" + suf) xs

    build "" "" s


/// <summary>
///     Styles a string with ANSI escape sequences.
/// </summary>
/// <param name="s">
///     The list of styles to turn into ANSI codes and apply to the result.
/// </param>
/// <param name="l">
///     The optional list of styles previously in effect.
/// </param>
/// <param name="d">
///     The string to stylise.
/// </param>
/// <returns>
///     The stylised (ANSI-escaped) string.
/// </param>
let ansiStylise s l d =
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

    let codify = List.map code >> String.concat ";"

    let prefix = "\u001b[" + codify s + "m"
    let suffix = "\u001b[" + withDefault "0" (Option.map codify l) + "m"
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
      ///     Whether or not we have escaped into a LaTeX command.
      /// </summary>
      InLatex : bool

      /// <summary>
      ///     The current style in use.
      /// </summary>
      CurrentStyle : (FontColor list) option

      /// <summary>
      ///     Whether or not we are emitting LaTeX.
      /// </summary>
      EmitLatex : bool

      /// <summary>
      ///     Whether or not styling is to be used.
      /// </summary>
      UseStyles : bool }

/// <summary>
///     The internal print function.
/// </summary>
/// <param name="state">The current state of the printer.</param>
/// <param name="doc">The document to print.</param>
/// <returns>
///     A function mapping <see cref="Doc"/>s to strings.
/// </returns>
let rec printState (state : PrintState) (doc : Doc) : string =
    match doc with
    | Header (heading, incmd) ->
        printState state heading + ":" + lnIndent state.Level + printState state incmd + lnIndent state.Level
    | Separator ->
        "----"
    | Styled (s, d) when state.UseStyles ->
        let state' = { state with InLatex = true; CurrentStyle = Some s }
        let stylise = if state.EmitLatex then latexStylise else ansiStylise
        let cmd = stylise s state.CurrentStyle (printState state' d)
        // Escape the first foray into LaTeX with $$, so it works with our
        // listings setup.
        if (not state.EmitLatex) || state.InLatex then cmd else sprintf "$%s$" cmd
    | Styled (s, d) ->
        printState state d
    | Latex (l, _) when state.EmitLatex ->
        let state' = { state with InLatex = true }
        let args = List.map (printState state' >> sprintf "{%s}") l.Args

        let name = sprintf "\\%s" l.Name
        let cmd = String.concat "" (name :: args)

        // Escape the first foray into LaTeX with $$, so it works with our
        // listings setup.
        if state.InLatex then cmd else sprintf "$%s$" cmd
    | Latex (_, r) -> printState state r
    | Verbatim x ->
        // TODO(CaptainHayashi): this is a nasty hack.
        let xd = printState state x
        if state.EmitLatex && state.InLatex
        then sprintf "\\texttt{%s}" xd
        else xd
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
let printStyled = printState { Level = 0; InLatex = false; CurrentStyle = None; UseStyles = true; EmitLatex = false }

/// <summary>
///     Prints a <see cref="Doc"/> with no styling.
/// </summary>
let printUnstyled = printState { Level = 0; InLatex = false; CurrentStyle = None; UseStyles = false; EmitLatex = false }


/// <summary>
///     Prints a <see cref="Doc"/>.
/// </summary>
let print (useColour : bool) (useLatex : bool) : Doc -> string =
    let initialState =
        { Level = 0
          InLatex = false
          CurrentStyle = None
          UseStyles = useColour
          EmitLatex = useLatex }
    printState initialState


(*
 * Shortcuts
 *)

let vsep xs = VSep(xs, Nop)
let hsepStr s c = HSep(c, String s)

/// Horizontally joins a list of commands with no separator.
let hjoin c = HSep(c, Nop)
/// Horizontally separates a list of commands with a space separator.
let hsep c = hsepStr " " c
/// Binary version of hsep.
let hsep2 sep x y =
    // Do a bit of optimisation in case we get long chains of hsep2s.
    match (x, y) with
    | HSep (xs, sx), HSep (ys, sy) when sx = sep && sy = sep ->
        HSep (Seq.append xs ys, sep)
    | HSep (xs, sx), y when sx = sep -> HSep (Seq.append xs (Seq.singleton y), sep)
    | x, HSep (ys, sy) when sy = sep -> HSep (Seq.append (Seq.singleton x) ys, sep)
    | x, y -> HSep (Seq.ofList [ x; y ], sep)
/// Infix version of hjoin.
let (<->) x y = hsep2 Nop x y
/// Infix version of hsep.
let (<+>) x y = hsep2 (String " ") x y
/// Horizontally separates a list of commands with commas.
let commaSep c = hsepStr ", " c
/// Infix version of commaSep.
/// This would be <,>, but that's a type error!
let (<&>) x y = hsep2 (String ", ") x y
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
let quoted = ssurround "'" "'"

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
    cmdHeaded (String "In" <+> String wholeDesc <+> quoted whole) [ err ]

/// <summary>
///     Prints an integer.
/// </summary>
let printInt (i : int) : Doc = String (sprintf "%i" i)
