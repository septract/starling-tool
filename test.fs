open System
open FParsec
open Microsoft.Z3

type Command =
    | Atomic of string
    | Skip
    | Seq of Command * Command
    | Choice of Command * Command
    | Par of Command * Command
    | Star of Command

type View =
    | Apply of View * args: string list
    | NamedView of string
    | Unit
    | Join of View * View

type Method =
    | End of postcondition: View
    | Step of precondition: View * cmd: Command

let wsc = anyOf " \t"
let ws = manyChars wsc
let ws1 = many1Chars wsc

let inBrackets bra ket = between (pstring bra .>> ws) (ws >>. pstring ket)
let inParens p = inBrackets "(" ")" p
let inBraces p = inBrackets "{" "}" p

let parseBin sep fn = pstring sep .>> ws >>% fun x y -> fn(x, y)

let parseCommand, parseCommandRef = createParserForwardedToRef<Command, unit>()
let parseAtomic = between (pstring "<") (pstring ">") (charsTillString ">" false 255) |>> Atomic
let parseSkip = pstring "skip" >>% Skip
let parseBracketedCommand = inParens parseCommand
let maybeAddStar x =
    match x with
        | (v, Some _) -> Star v
        | (v, None)   -> v
let parseSimpleCommand =
    choice [ parseAtomic
           ; parseSkip
           ; parseBracketedCommand
           ] .>>. ((pstring "*" |>> Some <|>% None) .>> ws) |>> maybeAddStar
do parseCommandRef :=
    chainl1 parseSimpleCommand
        (choice [ parseBin ";" Seq
                ; parseBin "||" Par
                ; parseBin "+" Choice
                ])

let notSpecial c = c <> ',' && c <> '(' && c <> ')' && c <> ' ' && c <> '\t' && c <> '{' && c <> '}'

let parseView, parseViewRef = createParserForwardedToRef<View, unit>()
let parseArgList = inParens (sepBy (many1Satisfy notSpecial) (ws >>. pstring "," .>> ws))
let parseNamedView = many1Satisfy notSpecial |>> NamedView
let parseUnit = pstring "emp" >>% Unit
let parseBracketedView = inParens parseView
let maybeAddArgs x =
    match x with
        | (v, Some args) -> Apply(v,args)
        | (v, None)      -> v
let parseSimpleView = 
    choice [ parseUnit
           ; parseBracketedView
           ; parseNamedView
           ] .>>. ((parseArgList |>> Some <|>% None) .>> ws) |>> maybeAddArgs
do parseViewRef :=
    chainl1 parseSimpleView (pstring "*" .>> ws >>% fun x y -> Join(x, y))

let parseViewLine = inBraces parseView

let cas =
    Choice(Atomic("foo"), Skip)

let test =
    Choice(cas, Star(Atomic("bar")))

let pv1 = "{ emp }"
let pv2 = "{ IsLock(l) * (HasTicket(l, t) * HasFoo) * emp * IsSword }"

// This is just a straight F# translation of the example code at
// https://github.com/Z3Prover/z3/blob/master/examples/dotnet/Program.cs
let runZ3Example =
    let ctx = new Context()

    Console.WriteLine("SudokuExample")

    // 9x9 matrix of integer variables
    let X : IntExpr[][] = Array.init 9 (fun i ->
        Array.init 9 (fun j -> 
           ctx.MkConst (ctx.MkSymbol (sprintf "x_%i_%i" (i + 1) (j + 1)), ctx.IntSort) :?> IntExpr
        )
    )

    // each cell contains a value in {1, ..., 9}
    let cells_c : BoolExpr[][] = Array.init 9 (fun i ->
        Array.init 9 (fun j ->
            ctx.MkAnd [| ctx.MkLe (ctx.MkInt 1, X.[i].[j])
                       ; ctx.MkLe (X.[i].[j], ctx.MkInt 9)
                      |]
        )
    )

    // each row contains a digit at most once
    let rows_c : BoolExpr[] = Array.init 9 (fun i ->
        ctx.MkDistinct (Array.init 9 (fun j -> X.[i].[j] :> Expr))
    )

    // each column contains a digit at most once
    let cols_c : BoolExpr[] = Array.init 9 (fun j ->
        let column = Array.init 9 (fun i -> X.[i].[j] :> Expr)
        ctx.MkDistinct column
    )

    // each 3x3 square contains a digit at most once
    let sq_c : BoolExpr[][] = Array.init 3 (fun i0 ->
        Array.init 3 (fun j0 ->
            let square : Expr[] = Array.init 3 (fun ij ->
                let i, j = Math.DivRem(ij, 3)
                X.[3 * i0 + i].[3 * j0 + j] :> Expr
            )
            ctx.MkDistinct square
        )
    )

    let mutable sudoku_c = ctx.MkTrue()
    for t in cells_c do
        sudoku_c <- ctx.MkAnd(ctx.MkAnd(t), sudoku_c)
    sudoku_c <- ctx.MkAnd(ctx.MkAnd(rows_c), sudoku_c)
    sudoku_c <- ctx.MkAnd(ctx.MkAnd(cols_c), sudoku_c)
    for t in sq_c do
        sudoku_c <- ctx.MkAnd(ctx.MkAnd(t), sudoku_c)

    // sudoku instance, we use '0' for empty cells
    let instance : int[,] =
        array2D [|
                  [|0;0;0;0;9;4;0;3;0|];
                  [|0;0;0;5;1;0;0;0;7|];
                  [|0;8;9;0;0;0;0;4;0|];
                  [|0;0;0;0;0;0;2;0;8|];
                  [|0;6;0;2;0;1;0;5;0|];
                  [|1;0;2;0;0;0;0;0;0|];
                  [|0;7;0;0;0;0;5;2;0|];
                  [|9;0;0;0;6;5;0;0;0|];
                  [|0;4;0;9;7;0;0;0;0|]
                |]

    let mutable instance_c = ctx.MkTrue()
    for i = 0 to 8 do
        for j = 0 to 8 do
            instance_c <-
                ctx.MkAnd [| instance_c;
                             ( ctx.MkITE ( ctx.MkEq (ctx.MkInt instance.[i, j], ctx.MkInt 0)
                                         , ctx.MkTrue()
                                         , (ctx.MkEq (X.[i].[j], ctx.MkInt instance.[i, j]))
                                         ) :?> BoolExpr
                             ) |]

    let s = ctx.MkSolver()
    s.Assert(sudoku_c)
    s.Assert(instance_c)

    if (s.Check() = Status.SATISFIABLE) then
        let m = s.Model
        let R : Expr[,] = Array2D.init 9 9 (fun i j -> m.Evaluate X.[i].[j])
        printfn "Sudoku solution:"
        for i = 0 to 8 do
            for j = 0 to 8 do
                printf " %A" R.[i, j]
            printfn ""
    else
        printfn "Failed to solve sudoku"

    ctx.Dispose

let main =
    Console.WriteLine("Hello, world!")
    match run parseCommand "<a := b> || <c := d>* + (<foo>; <bar>)" with
        | Success(result, _, _)   -> printfn "Success: %A" result
        | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg
    match run parseViewLine pv2 with
        | Success(result, _, _)   -> printfn "Success: %A" result
        | Failure(errorMsg, _, _) -> printfn "Failure: %s" errorMsg

    runZ3Example

main()
