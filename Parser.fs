namespace Starling

open FParsec

module Parser =
    let wsChars = " \t\r\n"
    let wsc : Parser<char, unit> = anyOf wsChars
    let ws = spaces // skips over " \t\r\n" by definition
    let ws1 = many1Chars wsc

    let inBrackets bra ket = between (pstring bra .>> ws) (ws >>. pstring ket)
    let inParens p = inBrackets "(" ")" p
    let inBraces p = inBrackets "{" "}" p
    let inAngles p = inBrackets "<" ">" p

    let parseBin sep fn = pstring sep .>> ws >>% fun x y -> fn(x, y)

    let parseView, parseViewRef = createParserForwardedToRef<View, unit>()
    let parseViewLine = inBraces parseView

    let parseCommand, parseCommandRef = createParserForwardedToRef<Command, unit>()
    let parseAtomic = inAngles (charsTillString ">" false 255) |>> Atomic
    let parseSkip = pstring "skip" >>% Skip
    let parseBracketedCommand = inParens parseCommand

    let maybeAddCondition lcond cmd rcond =
        match (lcond, rcond) with
            | (Some l, Some r) -> Viewed (BothViewCommand (l, cmd, r))
            | (None  , Some r) -> Viewed (PostViewCommand (cmd, r))
            | (Some l, None  ) -> Viewed (PreViewCommand  (l, cmd))
            | (None,   None  ) -> cmd
    let parseCondition = ws >>. opt parseViewLine .>> ws
    let tryWrapInCondition parser =
        pipe3 parseCondition parser parseCondition maybeAddCondition

    let maybeAddStar x =
        match x with
            | (v, Some _) -> Star v
            | (v, None)   -> v
    let parseStar = ws >>. opt (pstring "*") .>> ws
    let tryWrapInStar parser = parser .>>. parseStar |>> maybeAddStar
    let parseSimpleCommand =
        choice [parseAtomic; parseSkip; parseBracketedCommand]


    do parseCommandRef :=
        chainl1 (tryWrapInCondition (tryWrapInStar parseSimpleCommand))
            (choice [ parseBin ";" Seq
                    ; parseBin "||" Par
                    ; parseBin "+" Choice
                    ])

    let specChars = ",(){}*<>+|;"
    let notSpecial c = String.forall (fun d -> d <> c) (specChars + wsChars)
    let notSpecialWs c = String.forall (fun d -> d <> c) specChars

    let parseIdent = many1Satisfy notSpecial

    let parseArgList = inParens (sepBy (many1Satisfy notSpecialWs) (pstring "," .>> ws))
    let parseNamedView = parseIdent |>> NamedView
    let parseUnit = pstring "emp" >>% Unit
    let parseBracketedView = inParens parseView
    let maybeAddArgs x =
        match x with
            | (v, Some args) -> Apply(v,args)
            | (v, None)      -> v
    let tryWrapInApply parser = parser .>>. opt parseArgList .>> ws |>> maybeAddArgs
    let parseSimpleView = 
        choice [ parseUnit
               ; parseBracketedView
               ; parseNamedView
               ] 
    do parseViewRef :=
        chainl1 (tryWrapInApply parseSimpleView) (pstring "*" .>> ws >>% fun x y -> Join(x, y))

    let parseMethod =
        // Example method:               'main (argc, argv) { skip }'
        pipe3 (parseIdent .>> ws)     // 'main '
              (parseArgList .>> ws)   //      '(argc, argv) '
              (inBraces parseCommand) //                   '{ skip }'
              (fun n ps b -> { Name = n; Params = ps; Body = b })

    let demoParser parser line =
        match run parser line with
            | Success(result, _, _)   -> printfn "Success: %A" result
            | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg

    let demoCommand = demoParser parseCommand

    let parseScript = ws >>. sepEndBy parseMethod ws