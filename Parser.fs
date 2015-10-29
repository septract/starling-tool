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

    /// Helper for defining `chain1`s representing binary functions.
    /// When supplied as the chaining parser, tries to parse `op`, then
    /// whitespace, and finally passes the result to a `fn` as a pair.
    let parseBin op fn = pstring op .>> ws >>% fun x y -> fn(x, y)

    // High-level parser forwards.

    /// Parser for `raw` views (not surrounded in {braces}).
    let parseView, parseViewRef = createParserForwardedToRef<View, unit>()
    /// Parser for braced view statements.
    let parseViewLine = inViewBraces parseView

    /// Parser for commands.
    let parseCommand, parseCommandRef = createParserForwardedToRef<Command, unit>()

    // Command mini-parsers.

    /// Parser for atomic actions.
    let parseAtomic =
        // TODO(CaptainHayashi):
        //   as in Types.fs, this probably doesn't want to be a string
        inAngles (charsTillString ">" false 255) |>> Atomic

    /// Parser for `skip` commands.
    let parseSkip = pstring "skip" >>% Skip

    /// Parser for commands that are within (parens).
    let parseBracketedCommand = inParens parseCommand

    /// Takes a command, and two optional pre- and post-condition views, and
    /// potentially wraps the command in `Viewed` if the optional views exist.
    let maybeAddCondition lcond cmd rcond =
        match (lcond, rcond) with
            | (Some l, Some r) -> Viewed (BothViewCommand (l, cmd, r))
            | (None  , Some r) -> Viewed (PostViewCommand (cmd, r))
            | (Some l, None  ) -> Viewed (PreViewCommand  (l, cmd))
            | (None,   None  ) -> cmd

    /// Parser for optional condition views.
    let parseCondition = ws >>. opt parseViewLine .>> ws

    /// Takes a command parser and tries to parse pre- and post-condition views
    /// before and after it respectively.
    /// Wraps the parsed command in `Viewed` if such views exist.
    let tryWrapInCondition parser =
        pipe3 parseCondition parser parseCondition maybeAddCondition

    /// Takes a command and optional star, and potentially wraps the command in
    /// `Star` if the optional star (whose value is ignored) exists.
    let maybeAddStar cmd x =
        match x with
            | Some _ -> Star cmd
            | None   -> cmd

    /// Parser for optional command stars.
    let parseStar = ws >>. opt (pstring "*") .>> ws

    /// Takes a command parser and tries to parse a star after it.
    /// Wraps the parsed command in `Star` if a star exists.
    let tryWrapInStar parser =
        pipe2 parser parseStar maybeAddStar

    /// Parser for simple commands (atomics, skips, and bracketed commands).
    let parseSimpleCommand =
        choice [parseAtomic; parseSkip; parseBracketedCommand]

    do parseCommandRef :=
        chainl1 (tryWrapInCondition (tryWrapInStar parseSimpleCommand))
            (choice [ parseBin ";" Seq
                    ; parseBin "||" Par
                    ; parseBin "+" Choice
                    ])

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

    /// Parses a comma-delimited, parenthesised list.
    let parseArgList =
        // TODO(CaptainHayashi):
        //   Make this generic in the first argument to sepBy, and also
        //   make said first argument more robust -- currently this parses all
        //   whitespace before the ,!
        inParens (sepBy (many1Satisfy notSpecialWs) (pstring "," .>> ws))

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

    /// Parses a `simple` view (unit, bracketed, or named).
    let parseSimpleView = 
        choice [ parseUnit
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

        // Example method:               `main (argc, argv) { skip }`
        pipe3 (parseIdent .>> ws)     // `main `
              (parseArgList .>> ws)   //      `(argc, argv) `
              (inBraces parseCommand) //                   `{ skip }`
              (fun n ps b -> { Name = n; Params = ps; Body = b })

    /// Parses a script of zero or more methods, including leading and trailing whitespace.
    let parseScript =
        // TODO(CaptainHayashi): parse things that aren't methods:
        //   axioms definitions, etc
        ws >>. sepEndBy parseMethod ws
