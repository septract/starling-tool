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

    /// As pipe2, but with automatic whitespace parsing after each parser.
    let pipe2ws x y f = pipe2 (x .>> ws) (y .>> ws) f

    /// As pipe3, but with automatic whitespace parsing after each parser.
    let pipe3ws x y z f = pipe3 (x .>> ws) (y .>> ws) (z .>> ws) f

    // Special characters.

    /// All non-whitespace special characters.
    let specChars = ",(){}*<>+|;="

    // TODO(CaptainHayashi):
    //   these two predicates should probably have their names transposed!

    /// Predicate returning true if a character is not special or whitespace.
    let notSpecial c = String.forall (fun d -> d <> c) (specChars + wsChars)

    /// Predicate returning true if a character is not special.
    let notSpecialWs c = String.forall (fun d -> d <> c) specChars

    /// Parses a run of one or more non-special non-whitespace characters.
    let parseIdentifier = many1Satisfy notSpecial


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


    //
    // Forwards.
    //

    // These parsers are recursively defined, so we must set up
    // forwarding stubs to them before we can proceed with the
    // definitions.

    /// Parser for `raw` views (not surrounded in {braces}).
    let parseView, parseViewRef = createParserForwardedToRef<View, unit>()
    /// Parser for commands.
    let parseCommand, parseCommandRef = createParserForwardedToRef<Command, unit>()
    /// Parser for blocks.
    let parseBlock, parseBlockRef = createParserForwardedToRef<Block, unit>()
    /// Parser for expressions.
    /// The expression parser is split into several chains as per
    /// preference rank.
    let parseExpression, parseExpressionRef = createParserForwardedToRef<Expression, unit>()

    // From here on out, everything should line up more or less with the
    // BNF, except in reverse, bottom-up order.


    //
    // To be implemented.
    //

    /// Parser for atomic actions.
    let parseAtomic =
        // TODO(CaptainHayashi):
        //   as in Types.fs, this probably doesn't want to be a string
        charsTillString ">" false 255 |>> Atomic


    //
    // Parameters and lists.
    //

    /// Parses a comma-delimited parameter list.
    let parseParams =
        sepBy parseIdentifier (pstring "," .>> ws)
        // ^- {empty}
        //  | <identifier>
        //  | <identifier> , <params>

    /// Parses a comma-delimited, parenthesised parameter list.
    let parseParamList =
        // TODO(CaptainHayashi):
        //   Make this generic in the first argument to sepBy, and also
        //   make said first argument more robust -- currently this parses all
        //   whitespace before the ,!
        inParens parseParams
        // ^- ()
        //  | ( <params> )


    //
    // Expressions.
    //

    /// Parser for primary expressions.
    let parsePrimaryExpression =
        choice [ pstring "true"  >>% TrueExp
               ; pstring "false" >>% FalseExp
               ; pint64          |>> IntExp
               ; parseIdentifier |>> IdExp
               ; inParens parseExpression
               ] .>> ws

    /// Parser for multiplicative expressions.
    let parseMultiplicativeExpression =
        chainl1 (parsePrimaryExpression .>> ws)
                (choice
                    [ pstring "*" .>> ws >>% fun x y -> MulExp(x, y)
                    ; pstring "/" .>> ws >>% fun x y -> DivExp(x, y)
                    ]
                )

    /// Parser for additive expressions.
    let parseAdditiveExpression =
        chainl1 (parseMultiplicativeExpression .>> ws)
                (choice
                    [ pstring "+" .>> ws >>% fun x y -> AddExp(x, y)
                    ; pstring "-" .>> ws >>% fun x y -> SubExp(x, y)
                    ]
                )

    /// Parser for relational expressions.
    let parseRelationalExpression =
        chainl1 (parseAdditiveExpression .>> ws)
                (choice
                    [ pstring ">=" .>> ws >>% fun x y -> GeExp(x, y)
                    ; pstring "<=" .>> ws >>% fun x y -> LeExp(x, y)
                    ; pstring ">"  .>> ws >>% fun x y -> GtExp(x, y)
                    ; pstring "<"  .>> ws >>% fun x y -> LtExp(x, y)
                    ]
                )

    /// Parser for equality expressions.
    let parseEqualityExpression =
        chainl1 (parseRelationalExpression .>> ws)
                (choice
                    [ pstring "==" .>> ws >>% fun x y -> EqExp(x, y)
                    ; pstring "!=" .>> ws >>% fun x y -> NeqExp(x, y)
                    ]
                )

    /// Parser for logical AND expressions.
    let parseAndExpression =
        chainl1 (parseEqualityExpression .>> ws)
                (pstring "&&" .>> ws >>% fun x y -> AndExp(x, y))

    /// Parser for logical OR expressions.
    let parseOrExpression =
        chainl1 (parseAndExpression .>> ws)
                (pstring "||" .>> ws >>% fun x y -> OrExp(x, y))

    do parseExpressionRef := parseOrExpression

    //
    // Views.
    //

    /// Parses a view in parentheses.
    let parseBracketedView = inParens parseView

    /// Parses a conditional view.
    let parseIfView =
        pipe3ws (pstring "if" >>. ws >>. parseExpression)
                // ^- if <view-exprn> ...
                (pstring "then" >>. ws >>. parseView)
                // ^-                 ... then <view> ...
                (pstring "else" >>. ws >>. parseView .>> ws)
                // ^-                                 ... else <view>
                (fun c t f -> IfView(c, t, f))

    /// Takes a view and optional argument list, and potentially wraps the
    /// view in `Apply` if the optional argument list exists.
    let maybeAddApply view x =
        match x with
            | Some args -> Apply(view,args)
            | None      -> view

    /// Parses a possible argument list for an application of a parametric view.
    let parseApply = ws >>. opt parseParamList .>> ws

    /// Takes a view parser and tries to parse an argument list after it.
    /// Wraps the parsed command in `Apply` if an argument list exists.
    let tryWrapInApply parser = pipe2 parser parseApply maybeAddApply

    /// Parses a named view (identifier).
    let parseNamedView = parseIdentifier |>> NamedView

    /// Parses the unit view (`emp`, for our purposes).
    let parseUnit = pstring "emp" >>% Unit

    /// Parses a `basic` view (unit, if, named, or bracketed).
    let parseBasicView =
        choice [ parseUnit
                 // ^- `emp'
               ; parseIfView
                 // ^- if <view-exprn> then <view> else <view>
               ; tryWrapInApply parseNamedView
                 // ^- <identifier>
                 //  | <identifier> <param-list>
               ; parseBracketedView
                 // ( <view> )
               ]

    do parseViewRef :=
        chainl1 (tryWrapInApply parseBasicView)
                // ^- <basic-view>
                //  | <basic-view> ...
                (pstring "*" .>> ws >>% fun x y -> Join(x, y))
                //                 ... * <view>

    /// Parser for braced view statements.
    let parseViewLine = inViewBraces parseView
                        // ^- {| <view> |}

    //
    // Commands.
    //

    /// Parser for blocks.
    let parseParSet = (sepBy1 (parseBlock .>> ws) (pstring "||" .>> ws))
                      // ^- <block>
                      //  | <block> || <par-set>
                      |>> Blocks

    /// Parser for the 'while (expr)' leg of while and do-while commands.
    let parseWhileLeg =
        pstring "while" >>. ws >>. inParens parseExpression

    /// Parser for while (expr) block.
    let parseWhile = parseWhileLeg .>> ws .>>. parseBlock |>> While

    /// Parser for do (expr) while block.
    let parseDoWhile =
        pstring "do" >>. ws >>. parseBlock .>>. (ws >>. parseWhileLeg) |>> DoWhile

    /// Parser for if (expr) block else block.
    let parseIf = pipe3ws (pstring "if" >>. ws >>. inParens parseExpression)
                          (parseBlock .>> ws .>> pstring "else")
                          parseBlock
                          (fun c t f -> If(c, t, f))

    /// Parser for `skip` commands.
    /// Skip is inserted when we're in command position, but see a semicolon.
    let parseSkip = pstring ";" .>> ws >>% Skip
                    // ^- ;

    /// Parser for simple commands (atomics, skips, and bracketed commands).
    do parseCommandRef :=
        choice [ parseSkip
                 // ^- `;'
               ; inAngles parseAtomic .>> ws .>> pstring ";"
                 // ^- < <atomic> > ;
               ; parseIf
                 // ^- if ( <expression> ) <block> <block>
               ; parseDoWhile
                 // ^- do <block> while ( <expression> )
               ; parseWhile
                 // ^- while ( <expression> ) <block>
               ; parseParSet
                 // ^- <par-set>
               ]


    //
    // Blocks.
    //

    /// Parser for lists of semicolon-delimited, postconditioned
    /// commands.
    let parseCommands =
        many1 (
            pipe2ws parseCommand
                    // ^- <command> ...
                    parseViewLine
                    // ^-           ... <view-line>
                    (fun c v -> { Command = c; Post = v })
        )
        //  |             <command> ... <view-line> ... <commands>

    do parseBlockRef :=
        inBraces (
            // ^- {       ...                            ... }
            pipe2ws parseViewLine
                    // ^- ... <view-line> ...
                    parseCommands
                    //                    ... <commands> ...
                    (fun p c -> { Pre = p; Contents = c })
        )


    //
    // Top-level definitions.
    //

    /// Parses a constraint.
    let parseConstraint =
        pstring "constraint" >>. ws >>.
        // ^- constraint ..
            pipe2ws parseView
                    // ^- <view> ...
                    (pstring "=>" >>. ws >>. parseExpression .>> ws .>> pstring ";")
                    // ^-        ... => <expression> ;
                    (fun v ex -> { CView = v; CExpression = ex })

    /// Parses a single method, excluding leading or trailing whitespace.
    let parseMethod =
        pstring "method" >>. ws >>.
        // ^- method ...
            pipe3ws parseIdentifier
                    // ^- <identifier> ...
                    parseParamList
                    // ^-              ... <arg-list> ...
                    parseBlock
                    // ^-                             ... <block>
                    (fun n ps b -> { Name = n; Params = ps; Body = b })

    /// Parses a script of zero or more methods, including leading and trailing whitespace.
    let parseScript =
        // TODO(CaptainHayashi): parse things that aren't methods:
        //   axioms definitions, etc
        ws >>. manyTill (
            choice [ parseMethod |>> SMethod
                     // ^- method <identifier> <arg-list> <block>
                   ; parseConstraint |>> SConstraint
                     // ^- constraint <view> => <expression> ;
                   ]
        ) eof

