/// Types and functions for variables and variable maps.
module Starling.Var

open Microsoft
open Chessie.ErrorHandling
open Starling.Errors.Var

(*
 * LValues
 *
 * TODO(CaptainHayashi): add support for non-variable LValues.
 *)

/// An lvalue.
/// This is given a separate type in case we add to it later.
type LValue = 
    | LVIdent of string

/// Flattens a LV to a string.
let rec flattenLV = 
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    function 
    | LVIdent s -> s

/// Creates a reference to a Boolean lvalue.
/// This does NOT check to see if the lvalue exists!
let mkBoolLV (ctx : Z3.Context) lv = 
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> ctx.MkBoolConst

/// Creates a reference to an integer lvalue.
/// This does NOT check to see if the lvalue exists!
let mkIntLV (ctx : Z3.Context) lv = 
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> ctx.MkIntConst

(*
 * Types
 *)

/// A variable type.
type Type = 
    | Int
    | Bool

(*
 * Name rewrites
 *)

/// Rewrites the name of a constant to its pre-state form.
let rewritePre name = name + "!before"

/// Rewrites the name of a constant to its post-state form.
let rewritePost name = name + "!after"

/// Rewrites the name of a constant to its frame form.
let rewriteFrame name = name + "!r"

(*
 * Variable records
 *)

/// A typed inner record of a variable.
type TVar<'E when 'E :> Z3.Expr> = 
    { Expr : 'E
      PreExpr : 'E
      PostExpr : 'E
      FrameExpr : 'E }

/// A record of a variable in the program model.
type Var = 
    | Int of TVar<Z3.IntExpr>
    | Bool of TVar<Z3.BoolExpr>

/// Retrieves the type of a Var.
let varType var = 
    match var with
    | Var.Int _ -> Type.Int
    | Var.Bool _ -> Type.Bool

/// Erases the type information in a Var.
let eraseVar tv = 
    match tv with
    | Int iv -> 
        { Expr = iv.Expr :> Z3.Expr
          PreExpr = iv.PreExpr :> Z3.Expr
          PostExpr = iv.PostExpr :> Z3.Expr
          FrameExpr = iv.FrameExpr :> Z3.Expr }
    | Bool bv -> 
        { Expr = bv.Expr :> Z3.Expr
          PreExpr = bv.PreExpr :> Z3.Expr
          PostExpr = bv.PostExpr :> Z3.Expr
          FrameExpr = bv.FrameExpr :> Z3.Expr }

/// Converts a variable name and type to a Var.
let makeVar (ctx : Z3.Context) ty (name : string) = 
    match ty with
    | Type.Int -> 
        Var.Int { Expr = ctx.MkIntConst name
                  PreExpr = ctx.MkIntConst(rewritePre name)
                  PostExpr = ctx.MkIntConst(rewritePost name)
                  FrameExpr = ctx.MkIntConst(rewriteFrame name) }
    | Type.Bool -> 
        Var.Bool { Expr = ctx.MkBoolConst name
                   PreExpr = ctx.MkBoolConst(rewritePre name)
                   PostExpr = ctx.MkBoolConst(rewritePost name)
                   FrameExpr = ctx.MkBoolConst(rewriteFrame name) }

/// A variable map.
type VarMap = Map<string, Var>

/// Makes a variable map from a list of type-name pairs.
let makeVarMap (ctx : Z3.Context) lst = 
    lst
    |> List.map snd // Extract all names from the list.
    |> findDuplicates
    |> function 
    | [] -> List.foldBack (fun (ty, name) (map : VarMap) -> map.Add(name, makeVar ctx ty name)) lst Map.empty |> ok
    | ds -> List.map Duplicate ds |> Bad

/// Tries to combine two variable maps.
/// Fails if the environments are not disjoint.
/// Failures are in terms of VarMapError.
let combineMaps (a : VarMap) (b : VarMap) = 
    Map.fold (fun (sR : Result<VarMap, VarMapError>) name var -> 
        trial { 
            let! s = sR
            if s.ContainsKey name then return! (fail (Duplicate name))
            else return (s.Add(name, var))
        }) (ok a) b

/// Tries to look up a variable record in a variable map.
/// Failures are in terms of Some/None.
let tryLookupVar env = function 
    | LVIdent s -> Map.tryFind s env

//| _ -> LEBadLValue lvalue |> fail
/// Looks up a variable record in a variable map.
/// Failures are in terms of VarMapError.
let lookupVar env s = 
    s
    |> tryLookupVar env
    |> failIfNone (NotFound(flattenLV s))

(*
 * Fetch modes
 *)

/// A mode for the Fetch atomic action.
type FetchMode = 
    | Direct // <a = b>
    | Increment // <a = b++>
    | Decrement // <a = b-->
