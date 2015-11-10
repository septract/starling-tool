namespace Starling

open System
open Microsoft.Z3

open Chessie.ErrorHandling

open Starling.AST
open Starling.Collator
open Starling.Model

module Z3 =
    // TODO(CaptainHayashi): these could be generalised, use Chessie?

    /// Represents an error when converting a view.
    type ViewConversionError =
        | VNotConstrainable of AST.View

    /// Represents an error when converting an expression.
    type ExprConversionError =
        | EBadType of expr: Microsoft.Z3.Expr * gotType: string * wantType: string
        | EBadAST  of ast: AST.Expression * reason: string

    /// Represents an error when converting a constraint.
    type ConstraintConversionError =
        | CFView of ViewConversionError
        | CFExpr of ExprConversionError

    /// Tries to flatten a constraint LHS view AST into a multiset.
    let rec viewASTToSet vast =
        match vast with
            | Apply ( NamedView s, pars ) -> ok [ { VName = s; VParams = pars } ]
            | NamedView s                 -> ok [ { VName = s; VParams = []   } ]
            | Unit                        -> ok []
            | Join ( l, r )               -> joinViews l r
            | v                           -> fail <| VNotConstrainable vast
    /// Merges two sides of a view monoid in the AST into one multiset.
    and joinViews l r =
        lift2 ( fun l r -> List.concat [ l; r ] )
              ( viewASTToSet l )
              ( viewASTToSet r )

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

    /// If both sides of a pair are ok, return f applied to them.
    /// Else, return the errors.
    let pairBindMap f g lr =
        trial {
            let! l = f ( fst lr )
            let! r = f ( snd lr )
            return g ( l, r )
        }

    /// Converts a pair of arith-exps to Z3, then chains f onto them.
    let rec chainArithExprs ( ctx : Context )
                            ( f : ( ArithExpr * ArithExpr ) -> 'a )
                            ( pair : ( AST.Expression * AST.Expression ) )
                                : Result<'a, ExprConversionError> =
        pairBindMap ( arithExprToZ3 ctx ) f pair

    /// Converts a pair of bool-exps to Z3, then chains f onto them.
    and chainBoolExprs ctx f =
        pairBindMap ( boolExprToZ3 ctx ) f

    /// Converts a Starling Boolean expression to a Z3 predicate using
    /// the given Z3 context.
    and boolExprToZ3 ( ctx : Context ) expr =
        match expr with
            | TrueExp           -> ctx.MkTrue   () |> ok
            | FalseExp          -> ctx.MkFalse  () |> ok
            | LVExp    v        -> ctx.MkBoolConst ( flattenLV v ) |> ok
            | GtExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkGt   ) ( l, r )
            | GeExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkGe   ) ( l, r )
            | LeExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkLe   ) ( l, r )
            | LtExp    ( l, r ) -> chainArithExprs ctx ( ctx.MkLt   ) ( l, r )
            | EqExp    ( l, r ) -> chainBoolExprs  ctx ( ctx.MkEq   ) ( l, r )
            | NeqExp   ( l, r ) -> chainBoolExprs  ctx ( ctx.MkEq   >> ctx.MkNot ) ( l, r )
            | AndExp   ( l, r ) -> chainBoolExprs  ctx ( mkAnd2 ctx ) ( l, r )
            | OrExp    ( l, r ) -> chainBoolExprs  ctx ( mkOr2 ctx  ) ( l, r )
            | _                 -> fail <| EBadAST ( expr, "cannot be a Boolean expression" )

    /// Converts a Starling arithmetic expression ot a Z3 predicate using
    /// the given Z3 context.
    and arithExprToZ3 ( ctx : Context ) expr =
        match expr with
            | IntExp i        -> ( ( ctx.MkInt      i               ) :> ArithExpr ) |> ok
            | LVExp  v        -> ( ( ctx.MkIntConst ( flattenLV v ) ) :> ArithExpr ) |> ok
            | MulExp ( l, r ) -> chainArithExprs ctx ( mkMul2 ctx ) ( l, r )
            | DivExp ( l, r ) -> chainArithExprs ctx ( ctx.MkDiv  ) ( l, r )
            | AddExp ( l, r ) -> chainArithExprs ctx ( mkAdd2 ctx ) ( l, r )
            | SubExp ( l, r ) -> chainArithExprs ctx ( mkSub2 ctx ) ( l, r )
            | _               -> fail <| EBadAST ( expr, "cannot be an arithmetic expression" )

    /// Extracts constraints from a script.
    let scriptViewConstraints =
        List.choose (
            fun s ->
                match s with
                    | SMethod     _ -> None
                    | SConstraint c -> Some c
        )

    /// Maps f over e's messages.
    let mapMessages f =
        either ( fun pair -> Ok ( fst pair, List.map f ( snd pair ) ) )
               ( fun msgs -> List.map f msgs |> Bad )

    /// Extracts the view constraints from a CollatedScript, turning each into a
    /// Model.Constraint.
    let scriptViewConstraintsZ3 ctx cs =
        List.map (
            fun con -> trial {
                let! v = mapMessages CFView ( viewASTToSet con.CView )
                let! c = mapMessages CFExpr ( boolExprToZ3 ctx con.CExpression )
                return { CViews = v; CZ3 = c }
            }
        ) cs.Constraints |> collect

    /// Collates a script, grouping all like-typed ScriptItems together.
    let collate script =
        // We foldBack instead of fold to preserve the original order.
        List.foldBack (
            fun item collation ->
                match item with
                    | SMethod m     -> { collation with Methods     = m :: collation.Methods }
                    | SConstraint c -> { collation with Constraints = c :: collation.Constraints }
        ) script { Constraints = []; Methods = [] }

