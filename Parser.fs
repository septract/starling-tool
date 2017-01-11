/// <summary>
///     Parser for the Starling language.
/// </summary>
module Starling.Lang.Parser

open System

open FParsec
open Chessie.ErrorHandling

open Starling
open Starling.Collections
open Starling.Core.Symbolic
open Starling.Core.TypeSystem
open Starling.Core.Var
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
let lcom : Parser<unit, unit> = skipString "//" .>> skipRestOfLine true

/// Parser for skipping block comments.
let bcom, bcomImpl = createParserForwardedToRef()
do bcomImpl := skipString "/*" .>> skipManyTill (bcom <|> skipAnyChar) (skipString "*/")

/// Parser for skipping comments.
let com : Parser<unit, unit> = (lcom <|> bcom) <?> "comment"

/// Parser for skipping zero or more whitespace characters.
let ws : Parser<unit, unit> = skipMany (com <|> spaces1)

/// Parser accepting whitespace followed by a semicolon.
let wsSemi : Parser<unit, unit> = ws .>> pstring ";"

/// As pipe2, but with automatic whitespace parsing after each parser.
let pipe2ws x y f = pipe2 (x .>> ws) (y .>> ws) f

/// As pipe3, but with automatic whitespace parsing after each parser.
let pipe3ws x y z f = pipe3 (x .>> ws) (y .>> ws) (z .>> ws) f

/// Parses an identifier.
let parseIdentifier =
    (many1Chars2
        (pchar '_' <|> asciiLetter)
        (pchar '_' <|> asciiLetter <|> digit)) <?> "identifier"


// Bracket parsers.

/// Parser for items in a pair of matching brackets.
/// Automatically parses any whitespace after `bra`, and before `ket`.
let inBrackets bra ket = between (pstring bra .>> ws) (ws >>. pstring ket)
/// Parser for items in (parentheses).
let inParens p = inBrackets "(" ")" p
/// Parser for items in [brackets].
let inSquareBrackets p = inBrackets "[" "]" p
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
let parseView, parseViewRef =
    createParserForwardedToRef<View, unit> ()
/// Parser for view definitions.
let parseViewSignature, parseViewSignatureRef =
    createParserForwardedToRef<ViewSignature, unit> ()

/// Parser for commands.
let parseCommand, parseCommandRef =
    createParserForwardedToRef<Command<Marked<View>>, unit> ()
/// Parser for blocks.
let parseBlock, parseBlockRef
    = createParserForwardedToRef<Block<Marked<View>, Command<Marked<View>>>,
                                 unit> ()
/// Parser for expressions.
/// The expression parser is split into several chains as per
/// preference rank.
let parseExpression, parseExpressionRef =
    createParserForwardedToRef<Expression, unit> ()

// From here on out, everything should line up more or less with the
// BNF, except in reverse, bottom-up order.

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

/// Parses a non-empty comma-delimited parameter list.
let parseDefs argp =
    sepBy1 argp (pstring "," .>> ws)

/// Parses a comma-delimited, parenthesised parameter list.
let parseParamList argp =
    // TODO(CaptainHayashi):
    //   Make this generic in the first argument to sepBy, and also
    //   make said first argument more robust -- currently this parses all
    //   whitespace before the ,!
    inParens (parseParams argp)
    // ^- ()
    //  | ( <params> )

(*
 * Expressions.
 *)

/// Takes a Parser<'a, 'u> and gives back an annotated AST Node parser
/// Parser<Node<'a>, 'u> which will annotate with extra information from
/// the stream.
let nodify v =
    getPosition
    >>= fun p ->
        v |>> fun x -> { Position = { StreamName = p.StreamName; Line = p.Line; Column = p.Column; }
                         Node = x }

/// <summary>
///     Parser for symbolic sentences.
///
///     <para>
///         Symbolic sentences mix free strings and #-delimited parameter
///         references.
///     </para>
/// </summary>
let parseSymbolicSentence =
    many
        ((many1Chars (noneOf "}#") |>> SymString)
         <|> (pchar '#' >>. pint32 |>> SymParamRef))

/// <summary>
///     Parser for symbolic expressions.
///
///     <para>
///         Symbolic expressions are of the form
///         <c>%{sentence}(expr1, expr2, ..., exprN)</c>.
///     </para>
/// </summary>
let parseSymbolic =
    (pipe2ws
        (pstring "%" >>. inBraces parseSymbolicSentence)
        (parseParamList parseExpression)
        (fun s es -> { Sentence = s; Args = es })) <?> "symbolic"

/// Parser for primary expressions.
let parsePrimaryExpression =
    let expressions =
        (inParens parseExpression) :: List.map nodify [
            pstring "true" >>% True
            pstring "false" >>% False
            pint64 |>> Num
            parseIdentifier |>> Identifier
            parseSymbolic |>> Symbolic
    ]

    choice expressions .>> ws

/// Generic parser for tiers of binary expressions.
/// Accepts the next precedence level parser, and a list of pairs of operator and AST representation.
/// This generates a LEFT-associative precedence level.
let parseBinaryExpressionLevel nextLevel expList =
    let parseBopExpr (ops, op) =
        // TODO(CaptainHayashi): can this be solved without backtracking?
        nodify (pstring ops)
        .>>? ws
        (* A binary operator cannot ever be followed by a semicolon, + or -.
           This check removes ambiguity between > and <atomic braces>;,
           + and ++, and - and --. *)
        .>>? notFollowedBy (anyOf ";+-")
        |>> fun x -> fun a b -> { Node = BopExpr(op, a, b); Position = x.Position }
    chainl1 (nextLevel .>> ws)
            (choice
                (List.map parseBopExpr expList)
            )

/// Parser for postfix expressions.
let parsePostfixExpression, parsePostfixExpressionRef = createParserForwardedToRef<Expression, unit> ()
do parsePostfixExpressionRef :=
    let parseArraySubscript pex
        = nodify ((inSquareBrackets parseExpression <?> "array subscript")
                  >>= fun a -> preturn (ArraySubscript (pex, a)))
          <|> preturn pex

    parsePrimaryExpression .>> ws >>= parseArraySubscript


/// Parser for unary expressions 
/// TODO(CaptainHayashi): this is a bit hacky, could unify postfix / unary expr? 
let parseUnaryExpression = 
     parsePostfixExpression
     <|> 
     nodify (skipString "!" >>. ws >>. parsePostfixExpression |>> (fun x -> UopExpr (Neg, x )))  


/// Parser for multiplicative expressions.
let parseMultiplicativeExpression =
    parseBinaryExpressionLevel parseUnaryExpression
        [ ("*", Mul)
          ("/", Div)
          ("%", Mod) ]

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

/// Parser for logical IMPL expressions.
let parseImplExpression =
    parseBinaryExpressionLevel parseEqualityExpression
        [ ("=>", Imp) ]

/// Parser for logical AND expressions.
let parseAndExpression =
    parseBinaryExpressionLevel parseImplExpression
        [ ("&&", And) ]

/// Parser for logical OR expressions.
let parseOrExpression =
    parseBinaryExpressionLevel parseAndExpression
        [ ("||", Or) ]

do parseExpressionRef := parseOrExpression <?> "expression"


(*
 * Atomic actions.
 *)

/// Parser for compare-and-swaps.
/// This parser DOES NOT parse whitespace afterwards.
let parseCAS =
    pstring "CAS"
    >>. inParens (pipe3ws (parseExpression .>> ws .>> pstring ",")
                          (parseExpression .>> ws .>> pstring ",")
                          parseExpression
                          (curry3 CompareAndSwap))

/// Parser for fetch sigils.
let parseFetchSigil =
    choice [ pstring "++" >>% Increment
             pstring "--" >>% Decrement ] <|>% Direct

/// Parser for fetch right-hand-sides.
let parseFetch fetcher =
    pipe2ws parseExpression
            parseFetchSigil
            (fun fetchee sigil -> Fetch (fetcher, fetchee, sigil))

/// Parser for fetch actions.
let parseFetchOrPostfix =
    parseExpression
    .>> ws
    .>>. parseFetchSigil
    >>= function
        | (x, Direct) -> ws >>. pstring "=" >>. ws >>. parseFetch x
        | p -> Postfix p |> preturn

/// Parser for assume actions.
let parseAssume =
    pstring "assume" >>. ws >>. inParens parseExpression |>> Assume

/// Parser for local assignments.
let parseAssign =
    pipe2ws parseExpression
    // ^- <lvalue> ...
            (pstring "=" >>. ws >>. parseExpression)
                  //             ... = <expression> ;
            mkPair

/// Parser for havoc actions.
let parseHavoc =
    skipString "havoc" >>. ws >>. parseIdentifier

/// Parser for atomic actions.
let parseAtomic =
    choice [ (stringReturn "id" Id)
             // This needs to fire before parseFetchOrPostfix due to
             // ambiguity.
             parseSymbolic |>> SymAtomic
             parseHavoc |>> Havoc
             parseAssume
             parseCAS
             parseFetchOrPostfix ]
    |> nodify

/// Parser for a collection of atomic actions.
let parseAtomicSet =
    inAngles (
        // Either one atomic...
        (parseAtomic |>> List.singleton)
        <|>
        // ...or an atomic{} block.
        (inBraces (many (parseAtomic .>> wsSemi .>> ws))))

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

/// Parses a builtin primitive type.
let parseBuiltinPrimType : Parser<TypeLiteral, unit> =
    choice [
        stringReturn "int" TInt 
        stringReturn "bool" TBool
    ]

/// Parses a type identifier.
let parseType : Parser<TypeLiteral, unit> =
    let parsePrimType =
        parseBuiltinPrimType <|> (parseIdentifier |>> TUser)

    let parseArray = inSquareBrackets pint32 |>> curry TArray
    let parseSuffixes = many parseArray

    let rec applySuffixes ty suffixes =
        match suffixes with
        | [] -> ty
        | x::xs -> applySuffixes (x ty) xs

    pipe2ws parsePrimType parseSuffixes applySuffixes

/// Parses a parameter.
let parseParam : Parser<Param, unit> =
    let buildParam ty id = { ParamType = ty; ParamName = id }
    pipe2ws parseType parseIdentifier buildParam
    // ^ <type> <identifier>


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
            (curry3 View.If)

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

/// Parser for view expressions.
let parseViewExpr =
    inViewBraces
        ((stringReturn "?" Unknown .>> ws)
        <|> pipe2ws
                parseView
                (opt (stringReturn "?" ()))
                (fun v qm ->
                     match qm with
                     | Some () -> Questioned v
                     | None -> Unmarked v))
        // ^- {| <view> |}
        //  | {| <view> ? |}
        //  | {| ? |}


(*
 * View definitions.
 *)

/// Parses a functional view definition.
let parseStrFuncView = parseFunc parseIdentifier |>> ViewSignature.Func

/// Parses the unit view definition.
let parseDUnit = stringReturn "emp" ViewSignature.Unit

/// Parses a view iterator definition.
let parseIteratorDef = inSquareBrackets parseIdentifier

/// Parses an iterated item, feeding the two results to another function.
let parseIteratedContainer
  (parseInner : Parser<'Inner, unit>)
  (comb : string -> 'Inner -> 'Outer)
  : Parser<'Outer, unit> =
    pipe2ws
        (pstring "iter" >>. ws >>. parseIteratorDef)
        (parseInner)
        comb

/// Parses an iterated view definition.
let parseDIterated =
    parseIteratedContainer
        (parseFunc parseIdentifier)
        (fun e f -> ViewSignature.Iterated(f, e))

/// Parses a `basic` view definition (unit, if, named, or bracketed).
let parseBasicViewSignature =
    choice [ parseDUnit
             // ^- `emp'
             parseStrFuncView
             // ^- <identifier>
             //  | <identifier> <arg-list>
             inParens parseViewSignature ]
             // ( <view> )

do parseViewSignatureRef := parseViewLike parseBasicViewSignature ViewSignature.Join


(*
 * View prototypes.
 *)


/// Parses a view prototype (a LHS followed optionally by an iterator).
let parseViewProto =
    // TODO (CaptainHayashi): so much backtracking...
    (pstring "iter" >>. ws >>. 
      (parseFunc parseParam
         |>> (fun lhs -> WithIterator lhs))) 
    <|> 
      (parseFunc parseParam
         |>> (fun lhs -> NoIterator (lhs, false)))

/// Parses a set of one or more view prototypes.
let parseViewProtoSet =
    pstring "view" >>. ws >>. parseDefs parseViewProto .>> wsSemi

(*
 * Commands.
 *)

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
                 .>>. (ws >>. parseWhileLeg .>> wsSemi)
                 |>> DoWhile

/// Parser for if (expr) block else block.
let parseIf =
    pipe3ws (pstring "if" >>. ws >>. inParens parseExpression)
            parseBlock
            (opt (pstring "else" >>. ws >>. parseBlock))
            (curry3 If)

/// Parser for prim compositions.
let parsePrimSet =
    (* We can parse only one atomic, but any number of assigns before it.
       We must ensure there is a ; between the last assign and the atomic. *)
    pipe3 (many (parseAssign .>> wsSemi .>> ws))
          (* The atomic can be missing, and we can check unambiguously by
             trying to parse a < here. *)
          (opt (parseAtomicSet .>> wsSemi .>> ws))
          (many (parseAssign .>> wsSemi .>> ws))
          (fun lassigns atom rassigns ->
               { PreAssigns = lassigns
                 Atomics = withDefault [] atom
                 PostAssigns = rassigns }
               |> Prim)

/// Parser for `skip` commands.
/// Skip is inserted when we're in command position, but see a semicolon.
let parseSkip
    = stringReturn ";" (Prim { PreAssigns = []
                               Atomics = []
                               PostAssigns = [] })
    // ^- ;

/// Parser for simple commands (atomics, skips, and bracketed commands).
do parseCommandRef :=
    nodify <|
    (choice [parseSkip
             // ^- ;
             parseIf
             // ^- if ( <expression> ) <block> <block>
             parseDoWhile
             // ^- do <block> while ( <expression> )
             parseWhile
             // ^- while ( <expression> ) <block>
             parseParSet
             // ^- <par-set>
             parsePrimSet ])
             // ^- <prim-set>

(*
 * Blocks.
 *)

/// Parser for lists of semicolon-delimited, postconditioned
/// commands.
let parseCommands =
    many1
    <| pipe2ws parseCommand
               // ^- <command> ...
               parseViewExpr
               // ^-           ... <view-line>
               (fun c v -> { Command = c; Post = v })
               //  |             <command> ... <view-line> ... <commands>

do parseBlockRef :=
    inBraces
    <| pipe2ws parseViewExpr
        // ^- {       ...                            ... }
               // ^- ... <view-line> ...
               parseCommands
               //                    ... <commands> ...
               (fun p c -> { Pre = p; Contents = c })


(*
 * Top-level definitions.
 *)

/// Parses a constraint right-hand side.
let parseConstraintRhs : Parser<Expression option, unit> =
    choice [
        (stringReturn "?" None)
        (parseExpression |>> Some) ]
    // ^ ?
    // ^ %{ <symbol> %}
    // ^ <expression>

/// Parses a constraint.
let parseConstraint : Parser<ViewSignature * Expression option, unit> =
    pstring "constraint" >>. ws
    // ^- constraint ..
    >>. pipe3ws
            (parseDIterated <|> parseViewSignature)
            // ^- <view> ...
            (pstring "->")
            parseConstraintRhs
            (fun d _ v -> (d, v))
    .>> pstring ";"


/// parse an exclusivity constraint
let parseExclusive : Parser<List<StrFunc>, unit> = 
    pstring "exclusive" >>. ws
    // ^- exclusive ..  
    >>. parseDefs (parseFunc parseIdentifier)
    .>> wsSemi 
       
/// parse a disjointness constraint
let parseDisjoint : Parser<List<StrFunc>, unit> = 
    pstring "disjoint" >>. ws
    // ^- exclusive ..  
    >>. parseDefs (parseFunc parseIdentifier) 
    .>> wsSemi 
       

/// Parses a single method, excluding leading or trailing whitespace.
let parseMethod =
    pstring "method" >>. ws >>.
    // ^- method ...
        pipe2ws (parseFunc parseParam)
                // ^- <identifier> <arg-list> ...
                parseBlock
                // ^-                             ... <block>
                (fun s b -> {Signature = s ; Body = b} )

/// Parses a variable declaration with the given initial keyword and AST type.
let parseVarDecl kw (atype : VarDecl -> ScriptItem') =
    let parseList = parseParams parseIdentifier .>> wsSemi
    let buildVarDecl t vs = atype { VarType = t; VarNames = vs }
    pstring kw >>. ws >>. pipe2ws parseType parseList buildVarDecl

/// Parses a search directive.
let parseSearch =
    pstring "search" >>. ws
    // ^- search
                     >>. pint32
                     // ^- ... <depth>
                     .>> wsSemi

/// Parses a typedef.
let parseTypedef =
    // TODO(CaptainHayashi): forbid 'typedef bool int'.
    // TODO(CaptainHayashi): maybe one day permit 'typedef int[] heap'.
    // TODO(CaptainHayashi): maybe one day permit 'typedef typedef1 typedef2'.
    skipString "typedef"
    >>. ws >>.
    pipe2ws
        parseBuiltinPrimType
        parseIdentifier
        (fun ty id -> Typedef (ty, id))
    .>> wsSemi

/// Parses a pragma.
let parsePragma =
    skipString "pragma"
    >>. ws >>.
    pipe2ws
        parseIdentifier
        (inBraces (manyChars (noneOf "}")))
        (fun k v -> { Key = k; Value = v })
    .>> wsSemi

/// Parses a script of zero or more methods, including leading and trailing whitespace.
let parseScript =
    // TODO(CaptainHayashi): parse things that aren't methods:
    //   axioms definitions, etc
    ws >>. manyTill (choice (List.map nodify
                            [parsePragma |>> Pragma
                             // ^- pragma <identifier> { ... };
                             parseMethod |>> Method
                             // ^- method <identifier> <arg-list> <block>
                             parseConstraint |>> Constraint
                             // ^- constraint <view> -> <expression> ;
                             parseExclusive |>> Exclusive
                             // ^- exclusive <view>, <view>, ... ;
                             parseDisjoint |>> Disjoint
                             // ^- disjoint <view>, <view>, ... ;
                             parseViewProtoSet |>> ViewProtos
                             // ^- view <identifier> ;
                             //  | view <identifier> <view-proto-param-list> ;
                             parseSearch |>> Search
                             // ^- search 0;
                             parseTypedef
                             // ^- typedef int Node;
                             parseVarDecl "shared" SharedVars
                             // ^- shared <type> <identifier> ;
                             parseVarDecl "thread" ThreadVars]) .>> ws ) eof
                             // ^- thread <type> <identifier> ;

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
            | None ->
                eprintfn "note: no input filename given, reading from stdin"
                (Console.OpenStandardInput (), "(stdin)")
            | Some("-") -> (Console.OpenStandardInput (), "(stdin)")
            | Some(nam) -> (IO.File.OpenRead(nam) :> IO.Stream, nam)

        runParserOnStream parseScript () streamName stream Text.Encoding.UTF8
        |> function | Success (result, _, _) -> ok result
                    | Failure (errorMsg, _, _) -> fail errorMsg
    with
    | :? System.IO.FileNotFoundException  -> fail ("File not found: " + Option.get name)
