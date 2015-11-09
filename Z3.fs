namespace Starling

open System
open Microsoft.Z3

open Starling.AST
open Starling.Model

module Z3 =
    // TODO(CaptainHayashi): these could be generalised, use Chessie?

    /// Represents an error when converting a view.
    type ViewConversionError =
        | VNotConstrainable of AST.View

    /// Represents a multiset view conversion result.
    type ViewConversionResult =
        | VSuccess of Model.View list
        | VFail    of ViewConversionError

    /// Represents an error when converting an expression.
    type ExprConversionError =
        | EBadType of expr: Microsoft.Z3.Expr * gotType: string * wantType: string
        | EBadAST  of ast: AST.Expression * reason: string

    /// Represents a Z3 expression conversion result.
    type ExprConversionResult =
        | Bool  of Microsoft.Z3.BoolExpr
        | Arith of Microsoft.Z3.ArithExpr
        | EFail of ExprConversionError

    /// Represents an error when converting a constraint.
    type ConstraintConversionError =
        | CFView of ViewConversionError
        | CFExpr of ExprConversionError

    /// Represents a constraint conversion result.
    type ConstraintConversionResult =
        | CSuccess of Model.Constraint
        | CFail    of ConstraintConversionError

    /// Tries to flatten a constraint LHS view AST into a multiset.
    let rec viewASTToSet vast =
        match vast with
            | Apply ( NamedView s, pars ) -> VSuccess [ { VName = s; VParams = pars } ]
            | NamedView s                 -> VSuccess [ { VName = s; VParams = []   } ]
            | Unit                        -> VSuccess []
            | Join ( l, r )               -> joinViews l r
            | v                           -> VFail <| VNotConstrainable vast
    /// Merges two sides of a view monoid in the AST into one multiset.
    and joinViews l r =
        match viewASTToSet l, viewASTToSet r with
            | VSuccess sl, VSuccess sr -> VSuccess <| List.concat [ sl; sr ]
            | VFail    m , _           -> VFail m
            | _          , VFail m     -> VFail m

    /// Flattens a LV to a string.
    let rec flattenLV v =
        // TODO(CaptainHayashi): this is completely wrong, but we don't
        // have a semantics for it yet.
        match v with
            | LVIdent s  -> s
            | LVPtr   vv -> "*" + flattenLV vv

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
            | ( EFail l, _       ) -> EFail l
            | ( _      , EFail r ) -> EFail r
            | ( Bool  l, _       ) -> EFail <| EBadType ( l :> Microsoft.Z3.Expr, "bool", "arith" )
            | ( _      , Bool  r ) -> EFail <| EBadType ( r :> Microsoft.Z3.Expr, "bool", "arith" )

    /// Chains a pair of two successful boolean ConversionResults into a
    /// function returning a ConversionResult.
    let chainBools f lr =
        match lr with
            | ( Bool  l, Bool  r ) -> f ( l, r )
            | ( EFail l, _       ) -> EFail l
            | ( _      , EFail r ) -> EFail r
            | ( Arith l, _       ) -> EFail <| EBadType ( l :> Microsoft.Z3.Expr, "arith", "bool" )
            | ( _      , Arith r ) -> EFail <| EBadType ( r :> Microsoft.Z3.Expr, "arith", "bool" )

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
            | _                 -> EFail <| EBadAST ( expr, "cannot be a Boolean expression" )

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
            | _               -> EFail <| EBadAST ( expr, "cannot be an arithmetic expression" )

    /// Extracts constraints from a script.
    let scriptViewConstraints =
        List.choose (
            fun s ->
                match s with
                    | SMethod     _ -> None
                    | SConstraint c -> Some c
        )

    /// Extracts the view constraints from a Script, turning each into a
    /// Model.Constraint.
    let scriptViewConstraintsZ3 ctx =
        scriptViewConstraints >> List.map (
            fun con ->
                match viewASTToSet con.CView, boolExprToZ3 ctx con.CExpression with
                    | VSuccess v , Bool  c  -> CSuccess { CViews = v; CZ3 = c }
                    | VFail    ve, _        -> CFail <| CFView ve
                    | _          , Arith e  -> CFail <| CFExpr ( EBadType ( e :> Microsoft.Z3.Expr, "arith", "bool" ) )
                    | _          , EFail ee -> CFail <| CFExpr ee
        )
