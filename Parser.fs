/// Parser for the Starling language.
module Starling.Lang.Parser

open System

open FParsec
open Chessie.ErrorHandling

open Starling
open Starling.Collections
open Starling.Var
open Starling.Lang.AST

// Manually re-overload some FParsec operators Chessie overloaded.
let (>>=) = FParsec.Primitives.(>>=)

// General TODOs:
//   - TODO(CaptainHayashi): remove leftwards uses of ws
//   - TODO(CaptainHayashi): create and parse proper syntax definition
//   - TODO(CaptainHayashi): make more idiomatic!

// Whitespace.
//   TODO(CaptainHayashi): is some of this redundant?

/// Parser for skipping line comments.
let lcom = skipString "//" .>> skipRestOfLine true

/// Parser for skipping block comments.
let bcom = skipString "/*" .>> skipManyTill anyChar (skipString "*/")

/// Parser for skipping comments.
let com = (lcom <|> bcom) <?> "comment" 

/// Parser for skipping zero or more whitespace characters.
let ws = skipMany (com <|> spaces1)

/// As pipe2, but with automatic whitespace parsing after each parser.
let pipe2ws x y f = pipe2 (x .>> ws) (y .>> ws) f

/// As pipe3, but with automatic whitespace parsing after each parser.
let pipe3ws x y z f = pipe3 (x .>> ws) (y .>> ws) (z .>> ws) f

/// Parses an identifier.
let parseIdentifier = many1Chars2 (pchar '_' <|> asciiLetter)
                                  (pchar '_' <|> asciiLetter <|> digit)


// Bracket parsers.

/// Parser for items in a pair of matching brackets.
/// Automatically parses any whitespace after `bra`, and before `ket`.
let inBrackets bra ket = between (pstring bra .>> ws) (ws >>. pstring ket)
/// Parser for items in (parentheses).
let inParens p = inBrackets "(" ")" p
/// Parser for items in {braces}.
let inBraces p = inBrackets "{" "}" p
/// Parser for items in {|view braces|}.
let inViewBraces p = inBrackets "{|" "|}" p
/// Parser for items in <angle brackets>.
let inAngles p = inBrackets "<" ">" p


(*
 * Forwards.
 *)

// These parsers are recursively defined, so we must set up
// forwarding stubs to them before we can proceed with the
// definitions.

/// Parser for `raw` views (not surrounded in {braces}).
let parseView, parseViewRef = createParserForwardedToRef<View, unit> ()
/// Parser for view definitions.
let parseViewDef, parseViewDefRef = createParserForwardedToRef<ViewDef, unit> ()
/// Parser for commands.
let parseCommand, parseCommandRef = createParserForwardedToRef<Command, unit> ()
/// Parser for blocks.
let parseBlock, parseBlockRef = createParserForwardedToRef<Block, unit> ()
/// Parser for expressions.
/// The expression parser is split into several chains as per
/// preference rank.
let parseExpression, parseExpressionRef = createParserForwardedToRef<Expression, unit> ()

// From here on out, everything should line up more or less with the
// BNF, except in reverse, bottom-up order.


(*
 * Expressions.
 *)

/// Parser for lvalues.
let parseLValue, parseLValueRef = createParserForwardedToRef<LValue, unit> ()
do parseLValueRef :=
    //(pstring "*" >>. ws >>. parseLValue |>> LVPtr)
    //<|>
    (parseIdentifier |>> LVIdent)

/// Parser for primary expressions.
let parsePrimaryExpression =
    choice [ pstring "true" >>% True
             pstring "false" >>% False
             pint64 |>> Int
             parseLValue |>> LV
             inParens parseExpression ] .>> ws

/// Generic parser for tiers of binary expressions.
/// Accepts the next precedence level parser, and a list of pairs of operator and AST representation.
/// This generates a LEFT-associative precedence level.
let parseBinaryExpressionLevel nextLevel expList =
    chainl1 (nextLevel .>> ws)
            (choice
                (List.map (fun (ops, op) -> (pstring ops .>> ws >>% curry3 Bop op)) expList)
            )

/// Parser for multiplicative expressions.
let parseMultiplicativeExpression =
    parseBinaryExpressionLevel parsePrimaryExpression
        [ ("*", Mul)
          ("/", Div) ]

/// Parser for additive expressions.
let parseAdditiveExpression =
    parseBinaryExpressionLevel parseMultiplicativeExpression
        [ ("+", Add)
          ("-", Sub) ]

/// Parser for relational expressions.
let parseRelationalExpression =
    parseBinaryExpressionLevel parseAdditiveExpression
        [ (">=", Ge)
          ("<=", Le)
          (">" , Gt)
          ("<" , Lt) ]

/// Parser for equality expressions.
let parseEqualityExpression =
    parseBinaryExpressionLevel parseRelationalExpression
        [ ("==", Eq)
          ("!=", Neq) ]

/// Parser for logical AND expressions.
let parseAndExpression =
    parseBinaryExpressionLevel parseEqualityExpression
        [ ("&&", And) ]

/// Parser for logical OR expressions.
let parseOrExpression =
    parseBinaryExpressionLevel parseAndExpression
        [ ("||", Or) ]

do parseExpressionRef := parseOrExpression


(*
 * Atomic actions.
 *)

/// Parser for compare-and-swaps.
/// This parser DOES NOT parse whitespace afterwards.
let parseCAS =
    pstring "CAS"
    >>. inParens (pipe3ws (parseLValue .>> ws .>> pstring ",")
                          (parseLValue .>> ws .>> pstring ",")
                          parseExpression
                          (curry3 CompareAndSwap))

/// Parser for fetch sigils.
let parseFetchSigil =
    choice [ pstring "++" >>% Increment
             pstring "--" >>% Decrement ] <|>% Direct

/// Parser for fetch sources.
let parseFetchSrc =
    // We can't parse general expressions here, because they
    // eat the > at the end of the atomic and the sigil!
    (parseLValue |>> LV)
    <|> inParens parseExpression

/// Parser for fetch right-hand-sides.
let parseFetch fetcher =
    pipe2ws parseFetchSrc
            parseFetchSigil
            (fun fetchee sigil -> Fetch (fetcher, fetchee, sigil))

/// Parser for fetch actions.
let parseFetchOrPostfix =
    parseLValue
    .>> ws
    .>>. parseFetchSigil
    >>= function
        | (x, Direct) -> ws >>. pstring "=" >>. ws >>. parseFetch x
        | p -> Postfix p |> preturn

/// Parser for assume actions.
let parseAssume =
    pstring "assume" >>. ws >>. inParens parseExpression |>> Assume

/// Parser for atomic actions.
let parseAtomic =
    choice [ stringReturn "id" Id
             parseAssume
             parseCAS
             parseFetchOrPostfix ]


(*
 * Parameters and lists.
 *)

/// Parses a comma-delimited parameter list.
/// Each parameter is parsed by argp.
let parseParams argp =
    sepBy argp (pstring "," .>> ws)
    // ^- {empty}
    //  | <identifier>
    //  | <identifier> , <params>

/// Parses a comma-delimited, parenthesised parameter list.
let parseParamList argp =
    // TODO(CaptainHayashi):
    //   Make this generic in the first argument to sepBy, and also
    //   make said first argument more robust -- currently this parses all
    //   whitespace before the ,!
    inParens (parseParams argp)
    // ^- ()
    //  | ( <params> )

/// Parses a Func given the argument parser argp.
let parseFunc argp =
    pipe2ws parseIdentifier (parseParamList argp) (fun f xs -> {Name = f; Params = xs})

(*
 * View-likes (views and view definitions).
 *)

/// Parses a view-like thing, with the given basic parser and
/// joining constructor.
let parseViewLike basic join =
    chainl1 basic
            // ^- <basic-view>
            //  | <basic-view> ...
            (stringReturn "*" (curry join) .>> ws)
            //                 ... * <view>

(*
 * Types.
 *)

/// Parses a type identifier.
let parseType = stringReturn "int" Type.Int <|> stringReturn "bool" Type.Bool;

/// Parses a pair of type identifier and parameter name.
let parseTypedParam = parseType .>> ws .>>. parseIdentifier
                      //^ <type> <identifier>


(*
 * Views.
 *)

/// Parses a conditional view.
let parseIfView =
    pipe3ws (pstring "if" >>. ws >>. parseExpression)
            // ^- if <view-exprn> ...
            (pstring "then" >>. ws >>. parseView)
            // ^-                 ... then <view> ...
            (pstring "else" >>. ws >>. parseView)
            // ^-                                 ... else <view>
            (curry3 IfView)

/// Parses a functional view.
let parseFuncView = parseFunc parseExpression |>> View.Func

/// Parses the unit view (`emp`, for our purposes).
let parseUnit = stringReturn "emp" Unit

/// Parses a `basic` view (unit, if, named, or bracketed).
let parseBasicView =
    choice [ parseUnit
             // ^- `emp'
             parseIfView
             // ^- if <view-exprn> then <view> else <view>
             parseFuncView
             // ^- <identifier>
             //  | <identifier> <arg-list>
             inParens parseView ]
             // ( <view> )

do parseViewRef := parseViewLike parseBasicView Join

/// Parser for braced view statements.
let parseViewLine = inViewBraces parseView
                    // ^- {| <view> |}


(*
 * View definitions.
 *)

/// Parses a functional view definition.
let parseDFuncView = parseFunc parseIdentifier |>> ViewDef.Func

/// Parses the unit view definition.
let parseDUnit = stringReturn "emp" ViewDef.Unit

/// Parses a `basic` view definition (unit, if, named, or bracketed).
let parseBasicViewDef =
    choice [ parseDUnit
             // ^- `emp'
             parseDFuncView
             // ^- <identifier>
             //  | <identifier> <arg-list>
             inParens parseViewDef ]
             // ( <view> )

do parseViewDefRef := parseViewLike parseBasicViewDef ViewDef.Join


(*
 * View prototypes.
 *)

/// Parses a view prototype.
let parseViewProto = 
    pstring "view" >>. ws >>. parseFunc parseTypedParam .>> ws .>> pstring ";" .>> ws


(*
 * Commands.
 *)

/// Parser for assignments.
let parseAssign =
    pipe2ws parseLValue
    // ^- <lvalue> ...
            (pstring "=" >>. ws >>. parseExpression .>> ws .>> pstring ";")
                  //             ... = <expression> ;
            (curry Assign)

/// Parser for blocks.
let parseParSet =
    (sepBy1 (parseBlock .>> ws) (pstring "||" .>> ws)) |>> Blocks
    // ^- <block>
    //  | <block> || <par-set>

/// Parser for the 'while (expr)' leg of while and do-while commands.
let parseWhileLeg =
    pstring "while" >>. ws >>. inParens parseExpression

/// Parser for while (expr) block.
let parseWhile =
    parseWhileLeg .>> ws .>>. parseBlock |>> While

/// Parser for do (expr) while block.
let parseDoWhile =
    pstring "do" >>. ws
                 >>. parseBlock
                 .>>. (ws >>. parseWhileLeg .>> ws .>> pstring ";")
                 |>> DoWhile

/// Parser for if (expr) block else block.
let parseIf =
    pipe3ws (pstring "if" >>. ws >>. inParens parseExpression)
            (parseBlock .>> ws .>> pstring "else")
            parseBlock
            (curry3 If)

/// Parser for atomic commands (not the actions themselves; that is parseAtomic).
let parseAtomicCommand =
    inAngles parseAtomic .>> ws .>> pstring ";" |>> Atomic

/// Parser for `skip` commands.
/// Skip is inserted when we're in command position, but see a semicolon.
let parseSkip
    = stringReturn ";" Skip
    // ^- ;

/// Parser for simple commands (atomics, skips, and bracketed commands).
do parseCommandRef :=
    choice [parseSkip
            // ^- ;
            parseAtomicCommand
            // ^- < <atomic> > ;
            parseIf
            // ^- if ( <expression> ) <block> <block>
            parseDoWhile
            // ^- do <block> while ( <expression> )
            parseWhile
            // ^- while ( <expression> ) <block>
            parseParSet
            // ^- <par-set>
            parseAssign]
            // ^- <lvalue> = <expression>


(*
 * Blocks.
 *)

/// Parser for lists of semicolon-delimited, postconditioned
/// commands.
let parseCommands =
    many1
    <| pipe2ws parseCommand
               // ^- <command> ...
               parseViewLine
               // ^-           ... <view-line>
               (fun c v -> { Command = c; Post = v })
               //  |             <command> ... <view-line> ... <commands>

do parseBlockRef :=
    inBraces
    <| pipe2ws parseViewLine
        // ^- {       ...                            ... }
               // ^- ... <view-line> ...
               parseCommands
               //                    ... <commands> ...
               (fun p c -> { Pre = p; Contents = c })


(*
 * Top-level definitions.
 *)

/// Parses a constraint.
let parseConstraint =
    pstring "constraint" >>. ws >>.
    // ^- constraint ..
        pipe2ws parseViewDef
                // ^- <view> ...
                (pstring "->" >>. ws >>. parseExpression .>> ws .>> pstring ";")
                // ^-        ... -> <expression> ;
                (fun v ex -> {CView = v ; CExpression = ex} )

/// Parses a single method, excluding leading or trailing whitespace.
let parseMethod =
    pstring "method" >>. ws >>.
    // ^- method ...
        pipe2ws (parseFunc parseIdentifier)
                // ^- <identifier> <arg-list> ...
                parseBlock
                // ^-                             ... <block>
                (fun s b -> {Signature = s ; Body = b} )

/// Parses a variable with the given initial keyword.
let parseVar kw = pstring kw >>. ws
                  // ^- global     ...
                             >>. parseTypedParam
                             // ^- ... <type> <identifier> ...
                             .>> pstring ";"
                             // ^-                         ... ;

/// Parses a script of zero or more methods, including leading and trailing whitespace.
let parseScript =
    // TODO(CaptainHayashi): parse things that aren't methods:
    //   axioms definitions, etc
    ws >>. manyTill (choice [parseMethod |>> Method
                             // ^- method <identifier> <arg-list> <block>
                             parseConstraint |>> Constraint
                             // ^- constraint <view> => <expression> ;
                             parseViewProto |>> ViewProto
                             // ^- view <identifier> ;
                             //  | view <identifier> <view-proto-param-list> ;
                             parseVar "global" |>> Global
                             // ^- global <type> <identifier> ;
                             parseVar "local" |>> Local] .>> ws ) eof
                             // ^- local <type> <identifier> ;

(*
 * Frontend
 *)

/// Opens the file with the given name, parses it, and returns the AST.
/// The AST is given inside a Chessie result.
let parseFile name =
    try 
        // If - or no name was given, parse from the console.
        let stream, streamName =
            match name with
            | None | Some("-") -> (Console.OpenStandardInput (), "(stdin)")
            | Some(nam) -> (IO.File.OpenRead(nam) :> IO.Stream, nam)

        runParserOnStream parseScript () streamName stream Text.Encoding.UTF8
        |> function | Success (result, _, _) -> ok result
                    | Failure (errorMsg, _, _) -> fail errorMsg   
    with 
    | :? System.IO.FileNotFoundException  -> fail ("File not found: " + Option.get name)