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
    //| LVPtr of LValue

/// Flattens a LV to a string.
let rec flattenLV v =
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    match v with
    | LVIdent s -> s
    //| LVPtr vv -> "*" + flattenLV vv

/// Creates a reference to a Boolean lvalue.
/// This does NOT check to see if the lvalue exists!
let mkBoolLV (ctx: Z3.Context) lv =
    (* TODO(CaptainHayashi): when we support pointers, this will
     *                       need totally changing.
     *)
    lv
    |> flattenLV
    |> ctx.MkBoolConst

/// Creates a reference to an integer lvalue.
/// This does NOT check to see if the lvalue exists!
let mkIntLV (ctx: Z3.Context) lv =
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
    { VarExpr: 'E
      VarPreExpr: 'E
      VarPostExpr: 'E
      VarFrameExpr: 'E }

/// A record of a variable in the program model.
type Var =
    | IntVar of TVar<Z3.IntExpr>
    | BoolVar of TVar<Z3.BoolExpr>

/// Retrieves the type of a Var.
let varType var =
    match var with
    | IntVar _ -> Int
    | BoolVar _ -> Bool

/// Erases the type information in a Var.
let eraseVar tv =
    match tv with
    | IntVar iv -> { VarExpr = iv.VarExpr :> Z3.Expr
                     VarPreExpr = iv.VarPreExpr :> Z3.Expr
                     VarPostExpr = iv.VarPostExpr :> Z3.Expr
                     VarFrameExpr = iv.VarFrameExpr :> Z3.Expr }
    | BoolVar bv -> { VarExpr = bv.VarExpr :> Z3.Expr
                      VarPreExpr = bv.VarPreExpr :> Z3.Expr
                      VarPostExpr = bv.VarPostExpr :> Z3.Expr
                      VarFrameExpr = bv.VarFrameExpr :> Z3.Expr }


/// Converts a variable name and type to a Var.
let makeVar (ctx : Z3.Context) ty (name : string) =
    match ty with
    | Int ->
        IntVar { VarExpr = ctx.MkIntConst name
                 VarPreExpr = ctx.MkIntConst (rewritePre name)
                 VarPostExpr = ctx.MkIntConst (rewritePost name)
                 VarFrameExpr = ctx.MkIntConst (rewriteFrame name) }
    | Bool ->
        BoolVar { VarExpr = ctx.MkBoolConst name
                  VarPreExpr = ctx.MkBoolConst (rewritePre name)
                  VarPostExpr = ctx.MkBoolConst (rewritePost name)
                  VarFrameExpr = ctx.MkBoolConst (rewriteFrame name) }

/// A variable map.
type VarMap = Map<string, Var>

/// Makes a variable map from a list of type-name pairs.
let makeVarMap (ctx : Z3.Context) lst =
    let names = List.map snd lst
    match (findDuplicates names) with
    | [] -> ok <| List.foldBack
                    (fun (ty, name) (map: VarMap) ->
                         map.Add (name, makeVar ctx ty name))
                    lst
                    Map.empty
    | ds -> Bad <| List.map VMEDuplicate ds

/// Tries to combine two variable maps.
/// Fails if the environments are not disjoint.
/// Failures are in terms of VarMapError.
let combineMaps (a: VarMap) (b: VarMap) =
    Map.fold
        (fun (sR: Result<VarMap, VarMapError>) name var ->
            trial {
                let! s = sR

                if s.ContainsKey name
                then return! (fail (VMEDuplicate name))
                else return (s.Add (name, var))
            } )
        (ok a)
        b

/// Tries to look up a variable record in a variable map.
/// Failures are in terms of Some/None.
let tryLookupVar env lvalue =
    match lvalue with
    | LVIdent s -> Map.tryFind s env
    //| _ -> LEBadLValue lvalue |> fail

/// Looks up a variable record in a variable map.
/// Failures are in terms of VarMapError.
let lookupVar env s =
    s
    |> tryLookupVar env
    |> failIfNone (VMENotFound (flattenLV s))


(*
 * Fetch modes
 *)

/// A mode for the Fetch atomic action.
type FetchMode =
    | Direct     // <a = b>
    | Increment  // <a = b++>
    | Decrement  // <a = b-->
