namespace Starling

open FParsec

// General TODOs:
//   - TODO(CaptainHayashi): remove leftwards uses of ws
//   - TODO(CaptainHayashi): create and parse proper syntax definition
//   - TODO(CaptainHayashi): make more idiomatic!

module Parser =
    // Whitespace.
    //   TODO(CaptainHayashi): is some of this redundant?

    /// String containing all whitespace characters (as per `spaces`).
    let wsChars = " \t\r\n"
    /// Character parser accepting any character in `wsChars`.
    let wsc : Parser<char, unit> = anyOf wsChars
    /// Parser for skipping zero or more whitespace characters.
    let ws = spaces // skips over " \t\r\n" by definition
    /// Parser for skipping ONE or more whitespace characters.
    let ws1 = many1Chars wsc

    /// As pipe2, but with automatic whitespace parsing between the parsers.
    let pipe2ws x y f = pipe2 (x .>> ws) y f

    /// As pipe3, but with automatic whitespace parsing between the parsers.
    let pipe3ws x y z f = pipe3 (x .>> ws) (y .>> ws) z f

    // Special characters.

    /// All non-whitespace special characters.
    let specChars = ",(){}*<>+|;"

    // TODO(CaptainHayashi):
    //   these two predicates should probably have their names transposed!

    /// Predicate returning true if a character is not special or whitespace.
    let notSpecial c = String.forall (fun d -> d <> c) (specChars + wsChars)

    /// Predicate returning true if a character is not special.
    let notSpecialWs c = String.forall (fun d -> d <> c) specChars

    /// Parses a run of one or more non-special non-whitespace characters.
    let parseIdent = many1Satisfy notSpecial


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

    /// Parses a comma-delimited, parenthesised list.
    let parseArgList =
        // TODO(CaptainHayashi):
        //   Make this generic in the first argument to sepBy, and also
        //   make said first argument more robust -- currently this parses all
        //   whitespace before the ,!
        inParens (sepBy (many1Satisfy notSpecialWs) (pstring "," .>> ws))

    /// Helper for defining `chain1`s representing binary functions.
    /// When supplied as the chaining parser, tries to parse `op`, then
    /// whitespace, and finally passes the result to a `fn` as a pair.
    let parseBin op fn = pstring op .>> ws >>% fun x y -> fn(x, y)


    //
    // High-level parser forwards.
    //

    /// Parser for `raw` views (not surrounded in {braces}).
    let parseView, parseViewRef = createParserForwardedToRef<View, unit>()
    /// Parser for braced view statements.
    let parseViewLine = inViewBraces parseView

    /// Parser for commands.
    let parseCommand, parseCommandRef = createParserForwardedToRef<Command, unit>()

    /// Parser for blocks.
    let parseBlock, parseBlockRef = createParserForwardedToRef<Block, unit>()


    //
    // Commands
    //

    /// Parser for atomic actions.
    let parseAtomic =
        // TODO(CaptainHayashi):
        //   as in Types.fs, this probably doesn't want to be a string
        inAngles (charsTillString ">" false 255) |>> Atomic

    /// Parser for expressions.
    let parseExpression =
        // TODO(CaptainHayashi):
        //   as in Types.fs, this probably doesn't want to be a string
        charsTillString ")" false 255

    /// Parser for `skip` commands.
    /// Skip is inserted when we're in command position, but see a semicolon.
    let parseSkip = pstring ";" .>> ws >>% Skip

    /// Parser for blocks.
    let parseBlocks = (sepBy1 (parseBlock .>> ws) (pstring "||" .>> ws))
                      |>> Blocks

    /// Parser for if (expr) block else block.
    let parseIf = pipe3ws (pstring "if" >>. ws >>. inParens parseExpression)
                          (parseBlock .>> ws .>> pstring "else")
                          parseBlock
                          (fun c t f -> If(c, t, f))

    /// Parser for the 'while (expr)' leg of while and do-while commands.
    let parseWhileLeg =
        pstring "while" >>. ws >>. inParens parseExpression

    /// Parser for while (expr) block.
    let parseWhile = parseWhileLeg .>> ws .>>. parseBlock |>> While

    /// Parser for do (expr) while block.
    let parseDoWhile =
        pstring "do" >>. ws >>. parseBlock .>>. (ws >>. parseWhileLeg) |>> DoWhile

    /// Parser for simple commands (atomics, skips, and bracketed commands).
    do parseCommandRef :=
        choice [ parseAtomic .>> ws .>> pstring ";"
               ; parseIf
               ; parseDoWhile
               ; parseWhile
               ; parseBlocks
               ; parseSkip
               ]
    //
    // Blocks
    //

    /// Parser for semicolon-delimited, postconditioned commands.
    let parseViewedCommand =
        pipe2ws parseCommand
                parseViewLine
                (fun c v -> { Command = c; Post = v })

    do parseBlockRef :=
        inBraces (
            pipe2ws parseViewLine
                    (sepEndBy parseViewedCommand ws)
                //    parseViewLine
                    (fun p c -> { Pre = p; Contents = c })
        )

    //
    // Views
    //

    /// Parses a named view (identifier).
    let parseNamedView = parseIdent |>> NamedView

    /// Parses the unit view (`emp`, for our purposes).
    let parseUnit = pstring "emp" >>% Unit

    /// Parses a view in parentheses.
    let parseBracketedView = inParens parseView

    /// Takes a view and optional argument list, and potentially wraps the
    /// view in `Apply` if the optional argument list exists.
    let maybeAddApply view x =
        match x with
            | Some args -> Apply(view,args)
            | None     -> view

    /// Parses a possible argument list for an application of a parametric view.
    let parseApply = ws >>. opt parseArgList .>> ws

    /// Takes a view parser and tries to parse an argument list after it.
    /// Wraps the parsed command in `Apply` if an argument list exists.
    let tryWrapInApply parser = pipe2 parser parseApply maybeAddApply

    /// Eventually parse a view expression.
    let parseVExpression = charsTillString "then" false 255

    /// Parses a conditional view.
    let parseIfView =
        pipe3ws (pstring "if" >>. ws >>. parseVExpression)
                (pstring "then" >>. ws >>. parseView)
                (pstring "else" >>. ws >>. parseView .>> ws)
                (fun c t f -> IfView(c, t, f))

    /// Parses a `simple` view (unit, bracketed, or named).
    let parseSimpleView =
        choice [ parseUnit
               ; parseIfView
               ; parseNamedView
               ; parseBracketedView
               ]

    do parseViewRef :=
        chainl1 (tryWrapInApply parseSimpleView) (pstring "*" .>> ws >>% fun x y -> Join(x, y))

    /// Parses a single method, excluding leading or trailing whitespace.
    let parseMethod =
        // TODO(CaptainHayashi):
        //   we may later need to add more syntax to the beginning of method
        //   definitions (eg `method main (argc, argv) { skip }`)

        // Example method:             `method main (argc, argv) { skip }`
        pstring "method" >>. ws >>. // `method `
            pipe3ws parseIdent      //        `main `
                    parseArgList    //             `(argc, argv) `
                    parseBlock      //                          `{ skip }`
                    (fun n ps b -> { Name = n; Params = ps; Body = b })

    /// Parses a script of zero or more methods, including leading and trailing whitespace.
    let parseScript =
        // TODO(CaptainHayashi): parse things that aren't methods:
        //   axioms definitions, etc
        ws >>. sepEndBy parseMethod ws
