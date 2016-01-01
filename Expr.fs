/// Utilities for working with expressions.
module Starling.Expr

open Chessie.ErrorHandling
open Microsoft.Z3  // TODO(CaptainHayashi): temporary
open Starling.Var
open Starling.Model

// TODO(CaptainHayashi): this is where the non-Z3 Expr types will live.

/// Returns all of the exprs in es that are contained inside the expression e.
let rec exprsInExpr es (e : Expr) : Set<Expr> = 
    // Is this expression the same as any expressions in es?
    let self = es |> Set.filter e.Equals
    
    // Are any of the expressions inside e the same?
    let inner = 
        e.Args
        |> Set.ofArray
        |> unionMap (exprsInExpr es)
    self + inner

/// Extracts the post-states of the given environment.
let aftersOfEnv map = 
    map
    |> Map.toSeq
    |> Seq.map (snd
                >> eraseVar
                >> fun v -> v.PostExpr)
    |> Set.ofSeq

/// Extracts all the post-state variables in the model.
let aftersInModel model = 
    let g = aftersOfEnv model.Globals
    let l = aftersOfEnv model.Locals
    g + l

/// For a given expression, finds all the bound post-state variables.
let aftersInExpr model = exprsInExpr (aftersInModel model)

/// For a given expression, finds all the unbound post-state variables.
let aftersNotInExpr model expr = aftersInModel model - aftersInExpr model expr

/// Substitutes a different version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarTo sel env (expr : #Expr) var = 
    lookupVar env var |> either (fst
                                 >> eraseVar
                                 >> fun v -> expr.Substitute(v.Expr, sel v)) (fun _ -> expr :> Expr)

/// Substitutes the before version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarToBefore e = envVarTo (fun v -> v.PreExpr) e

/// Substitutes the after version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarToAfter e = envVarTo (fun v -> v.PostExpr) e

/// Performs the given substitution for all variables in the
/// given sequence.
let subAllInSeq env sq sub expr = Seq.fold (sub env) expr sq

/// Performs the given substitution for all variables in the
/// environment.
let subAllInEnv env = 
    // TODO(CaptainHayashi): the conversion to LVIdent is indicative of
    // the lack of pointer support, and needs to go when we add it.
    subAllInSeq env (env
                     |> Map.toSeq
                     |> Seq.map (fst >> LVIdent))

/// Performs the given substitution for all variables in the model.
let subAllInModel model sub expr = 
    expr
    |> subAllInEnv model.Globals sub
    |> subAllInEnv model.Locals sub