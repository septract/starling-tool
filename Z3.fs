namespace Starling

open System
open Microsoft.Z3

module Z3 =
    /// Flattens a LV to a string.
    let rec flattenLV v =
        // TODO(CaptainHayashi): this is completely wrong, but we don't
        // have a semantics for it yet.
        match v with
            | LVIdent s  -> s
            | LVPtr   vv -> "*" + flattenLV vv

    /// Represents a Z2 conversion result.
    type ConversionResult =
        | Bool  of BoolExpr
        | Arith of ArithExpr
        | Fail  of string

    /// Makes an And out of a pair of two expressions.
    let mkAnd2 (ctx: Context) lr = ctx.MkAnd [| fst lr; snd lr |]
    /// Makes an Or out of a pair of two expressions.
    let mkOr2 (ctx: Context) lr = ctx.MkOr [| fst lr; snd lr |]
    /// Makes an Add out of a pair of two expressions.
    let mkAdd2 (ctx: Context) lr = ctx.MkAdd [| fst lr; snd lr |]
    /// Makes a Sub out of a pair of two expressions.
    let mkSub2 (ctx: Context) lr = ctx.MkSub [| fst lr; snd lr |]
    /// Makes a Mul out of a pair of two expressions.
    let mkMul2 (ctx: Context) lr = ctx.MkMul [| fst lr; snd lr |]

    /// Chains a pair of two successful arithmetic ConversionResults into a
    /// function returning a ConversionResult.
    let chainAriths f lr =
        match lr with
            | ( Arith l, Arith r ) -> f ( l, r )
            | ( Fail  l, _       ) -> Fail l
            | ( _      , Fail  r ) -> Fail r
            | ( Bool  l, _       ) -> Fail "lhs is bool, expected arith"
            | ( _      , Bool  r ) -> Fail "rhs is bool, expected arith"

    /// Chains a pair of two successful boolean ConversionResults into a
    /// function returning a ConversionResult.
    let chainBools f lr =
        match lr with
            | ( Bool  l, Bool  r ) -> f ( l, r )
            | ( Fail  l, _       ) -> Fail l
            | ( _      , Fail  r ) -> Fail r
            | ( Arith l, _       ) -> Fail "lhs is arith, expected bool"
            | ( _      , Arith r ) -> Fail "rhs is arith, expected bool"

    /// Applies f to both items in a pair.
    let pairMap f lr = ( fst lr |> f, snd lr |> f )

    /// Converts a pair of arith-exps to Z3, then chains f onto them.
    let rec chainArithExprs ctx f =
        pairMap ( arithExprToZ3 ctx ) >> chainAriths f

    /// Converts a pair of bool-exps to Z3, then chains f onto them.
    and chainBoolExprs ctx f =
        pairMap ( boolExprToZ3 ctx ) >> chainBools f

    /// Converts a Starling Boolean expression to a Z3 predicate using
    /// the given Z3 context.
    and boolExprToZ3 ( ctx : Context ) expr =
        match expr with
            | TrueExp           -> ctx.MkTrue   ()                 |> Bool
            | FalseExp          -> ctx.MkFalse  ()                 |> Bool
            | LVExp    v        -> ctx.MkBoolConst ( flattenLV v ) |> Bool
            | GtExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkGt   >> Bool ) ( l, r )
            | GeExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkGe   >> Bool ) ( l, r )
            | LeExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkLe   >> Bool ) ( l, r )
            | LtExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkLt   >> Bool ) ( l, r )
            | EqExp    ( l, r ) -> chainBoolExprs  ctx ( ctx.MkEq   >> Bool ) ( l, r )
            | NeqExp   ( l, r ) -> chainBoolExprs  ctx ( ctx.MkEq   >> ctx.MkNot >> Bool ) ( l, r )
            | AndExp   ( l, r ) -> chainBoolExprs  ctx ( mkAnd2 ctx >> Bool ) ( l, r )
            | OrExp    ( l, r ) -> chainBoolExprs  ctx ( mkOr2 ctx  >> Bool ) ( l, r )
            | _           -> Fail "expected bool expr, got arith expr"

    /// Converts a Starling arithmetic expression ot a Z3 predicate using
    /// the given Z3 context.
    and arithExprToZ3 ( ctx : Context ) expr =
        match expr with
            | IntExp i        -> ( ( ctx.MkInt      i               ) :> ArithExpr ) |> Arith
            | LVExp  v        -> ( ( ctx.MkIntConst ( flattenLV v ) ) :> ArithExpr ) |> Arith
            | MulExp ( l, r ) -> chainArithExprs ctx ( mkMul2 ctx >> Arith ) ( l, r )
            | DivExp ( l, r ) -> chainArithExprs ctx ( ctx.MkDiv  >> Arith ) ( l, r )
            | AddExp ( l, r ) -> chainArithExprs ctx ( mkAdd2 ctx >> Arith ) ( l, r )
            | SubExp ( l, r ) -> chainArithExprs ctx ( mkSub2 ctx >> Arith ) ( l, r )
            | _         -> Fail "expected arith expr, got bool expr"

    /// Extracts constraints from a script.
    let scriptViewConstraints =
        List.choose (
            fun s ->
                match s with
                    | SMethod     _ -> None
                    | SConstraint c -> Some c
        )

    /// Extracts the view constraints from a Script, turning each into a
    /// pair of view and Z3 predicate.
    let scriptViewConstraintsZ3 ctx =
        scriptViewConstraints >> List.map (
            fun con -> ( con.CView, boolExprToZ3 ctx con.CExpression )
        )


    // This is just a straight F# translation of the example code at
    // https://github.com/Z3Prover/z3/blob/master/examples/dotnet/Program.cs
    let runZ3Example () =
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
