namespace Starling

open System
open Microsoft.Z3

open Chessie.ErrorHandling

open Starling.AST
open Starling.Collator
open Starling.Model

module Z3 =
    // TODO(CaptainHayashi): more consistent constructor names

    /// Represents an error when converting a view.
    type ViewError =
        | VENotFlat of AST.ViewDef

    /// Represents an error when converting an expression.
    type ExprError =
        | EEBadAST  of ast: AST.Expression * reason: string

    /// Represents an error when converting a constraint.
    type ConstraintError =
        | CEView of ViewError
        | CEExpr of ExprError

    /// Represents an error when converting a variable list.
    type VarError =
        | VEDuplicate of string

    /// Represents an error when converting a model.
    type ModelError =
        | MEConstraint of ConstraintError
        | MEVar        of VarError

    /// Tries to flatten a view definition AST into a multiset.
    let rec viewDefToSet vast =
        match vast with
            | DFunc ( s, pars ) -> ok [ { VName = s; VParams = pars } ]
            | DUnit             -> ok []
            | DJoin ( l, r )    -> joinViewDefs l r
    /// Merges two sides of a view monoid in the AST into one multiset.
    and joinViewDefs l r =
        lift2 ( fun l r -> List.concat [ l; r ] )
              ( viewDefToSet l )
              ( viewDefToSet r )

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

    /// Converts a pair of arith-exps to Z3, then chains f onto them.
    let rec chainArithExprs ( ctx : Context )
                            ( f : ( ArithExpr * ArithExpr ) -> 'a )
                            ( pair : ( AST.Expression * AST.Expression ) )
                                : Result<'a, ExprError> =
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
            | _                 -> fail <| EEBadAST ( expr, "cannot be a Boolean expression" )

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
            | _               -> fail <| EEBadAST ( expr, "cannot be an arithmetic expression" )

    /// Extracts the view constraints from a CollatedScript, turning each into a
    /// Model.Constraint.
    let scriptViewConstraintsZ3 ctx cs =
        List.map (
            fun con -> trial {
                let! v = mapMessages CEView ( viewDefToSet con.CView )
                let! c = mapMessages CEExpr ( boolExprToZ3 ctx con.CExpression )
                return { CViews = v; CZ3 = c }
            }
        ) cs.CConstraints |> collect

    /// Tries to find duplicate entries in a list.
    /// Returns a list of the duplicates found.
    let findDuplicates =
        List.groupBy id
            >> List.choose (
                fun xs ->
                    match xs with
                        | ( _, []    ) -> None
                        | ( _, [ _ ] ) -> None
                        | ( x, _     ) -> Some x
              )

    /// Converts a variable type to a Z3 sort.
    let typeToZ3 ( ctx : Context ) ty =
        match ty with
            | Int  -> ctx.IntSort  :> Sort
            | Bool -> ctx.BoolSort :> Sort

    /// Converts a AST variable list to Var record lists.
    let modelVarList ( ctx : Context ) lst =
        let names = List.map snd lst
        match ( findDuplicates names ) with
            | [] ->
                ok (
                    List.foldBack (
                        fun x ( map : Map<string, Var> ) ->
                            let sort = typeToZ3 ctx ( fst x )
                            map.Add ( snd x
                                    , { VarType = sort
                                        VarExpr = ctx.MkConst ( snd x, sort )
                                      }
                                    )
                    ) lst Map.empty
                )
            | ds -> Bad <| List.map VEDuplicate ds

    /// Converts a collated script to a model.
    let model ctx collated =
        trial {
            let! constraints = mapMessages MEConstraint ( scriptViewConstraintsZ3 ctx collated )
            let! globals     = mapMessages MEVar        ( modelVarList ctx collated.CGlobals )
            let! locals      = mapMessages MEVar        ( modelVarList ctx collated.CLocals )
            // TODO(CaptainHayashi): axioms, etc.

            return {
                Globals  = globals
                Locals   = locals
                DefViews = constraints
            }
        }

(*
    /// Tries to convert an inline view AST into a CondView.
    let viewASTToCond vast =
        // TODO(CaptainHayashi): currently we allow only one level of conditionality.
        match vast with
            | IfView expast lview rview ->
                match boolExprToZ3 ctx east, viewDefToSet last, viewDefToSet rast with
                    | EBool  e, VSuccess l, VSuccess r -> CITEView ( e, l, r )
                    | EArith e, _         , _          ->


    /// Finds the atomic commands in a Script, turning each into a
    /// Model.Axiom.
    let scriptAxioms ctx =
*)