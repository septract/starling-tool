/// Module containing the semantic definitions of commands.
module Starling.Semantics

open Microsoft.Z3
open Chessie.ErrorHandling
open Starling.AST
open Starling.Model
open Starling.Modeller

//
// Atomic emitters
//

/// Erases the type information in a Var.
let eraseVar tv =
    match tv with
    | IntVar iv -> { VarExpr = iv.VarExpr :> Expr
                     VarPreExpr = iv.VarPreExpr :> Expr
                     VarPostExpr = iv.VarPostExpr :> Expr
                     VarFrameExpr = iv.VarFrameExpr :> Expr }
    | BoolVar bv -> { VarExpr = bv.VarExpr :> Expr
                      VarPreExpr = bv.VarPreExpr :> Expr
                      VarPostExpr = bv.VarPostExpr :> Expr
                      VarFrameExpr = bv.VarFrameExpr :> Expr }

/// Returns all of the exprs in es that are contained inside the expression e.
let rec exprsInExpr es (e: Expr): Set<Expr> =
    // Is this expression the same as any expressions in es?
    let self = es
               |> Set.filter e.Equals
    // Are any of the expressions inside e the same?
    let inner = e.Args
                |> Set.ofArray
                |> unionMap (exprsInExpr es)
    self + inner

/// Extracts the post-states of the given environment.
let aftersOfEnv map =
    map
    |> Map.toSeq
    |> Seq.map (snd >> eraseVar >> fun v -> v.VarPostExpr)
    |> Set.ofSeq

/// Extracts all the post-state variables in the model.
let aftersInModel model =
    let g = aftersOfEnv model.Globals
    let l = aftersOfEnv model.Locals
    g + l
     
/// For a given expression, finds all the bound post-state variables.
let aftersInExpr model = exprsInExpr (aftersInModel model)

/// For a given expression, finds all the unbound post-state variables.
let aftersNotInExpr model expr =
    aftersInModel model - aftersInExpr model expr

/// Substitutes a different version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarTo sel env (expr: #Expr) var =
    lookupVar env var
    |> either (fst >> eraseVar >> fun v -> expr.Substitute (v.VarExpr, sel v))
              (fun _ -> expr :> Expr)

/// Substitutes the before version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarToBefore = envVarTo (fun v -> v.VarPreExpr)

/// Substitutes the after version of a variable in an expression.
/// Returns the expression unchanged if the requested variable does not
/// exist.
let envVarToAfter = envVarTo (fun v -> v.VarPostExpr)

/// Performs the given substitution for all variables in the
/// given sequence.
let subAllInSeq env sq sub expr = Seq.fold (sub env) expr sq

/// Performs the given substitution for all variables in the
/// environment.
let subAllInEnv env =
    // TODO(CaptainHayashi): the conversion to LVIdent is indicative of
    // the lack of pointer support, and needs to go when we add it.
    subAllInSeq env (env |> Map.toSeq |> Seq.map (fst >> LVIdent))

/// Performs the given substitution for all variables in the model.
let subAllInModel model sub expr =
    expr
    |> subAllInEnv model.Globals sub
    |> subAllInEnv model.Locals sub

/// Makes the relation after!after = before!before.
let makeRel model before after =
    let beforeB = subAllInModel model envVarToBefore before
    let afterA = subAllInModel model envVarToAfter after
    model.Context.MkEq (afterA, beforeB)

/// Given e, returns e!after = e!before.
let makeNoChange model expr =
    let exprA = subAllInModel model envVarToAfter expr
    let exprB = subAllInModel model envVarToBefore expr
    model.Context.MkEq (exprA, exprB)

/// Given some ArithExpr over a lvalue, return the relation for the
/// operation identified by the given fetch mode on that lvalue.
let makeFetchUpdate model (expr: ArithExpr) mode =
    let ctx = model.Context

    let exprB = (subAllInModel model envVarToBefore (expr :> Expr)) :?> ArithExpr
    let exprA = (subAllInModel model envVarToAfter (expr :> Expr)) :?> ArithExpr
    let exprMod = match mode with
                  // 'expr' -> expr!after = expr!before.
                  | Direct -> exprB
                  // 'expr++' -> expr!after = expr!before + 1.
                  | Increment -> mkAdd2 ctx (exprB, ctx.MkInt 1 :> ArithExpr)
                  // 'expr--' -> expr!after = expr!before - 1.
                  | Decrement -> mkSub2 ctx (exprB, ctx.MkInt 1 :> ArithExpr)
    ctx.MkEq (exprA, exprMod)

/// Emits Z3 corresponding to a compare-and-swap.
let makeCAS model destE testE setE =
    let ctx = model.Context

    (* Compare-and-swap gets its semantics in two steps:
     * 1) Success--dest becomes set; test held.
     * 2) Failure--test becomes dest; dest held.
     * In both cases, set is not modified.
     *)

    // Make the before-case versions of dest and test.
    let destEB = (subAllInModel model envVarToBefore destE)
    let testEB = (subAllInModel model envVarToBefore testE)
    let setEB = (subAllInModel model envVarToBefore setE)

    (* Now we make the cases.
     * Each case is in the form (cond => destAfter ^ testAfter).
     * We start with the success case.
     *)
    let succCond = ctx.MkEq (destEB, setEB)
    // In a success, we have destE!after = setE!before;
    let succDest = makeRel model setE destE
    // and test!after = test!before.
    let succTest = makeNoChange model testE
    let succSem = mkAnd2 ctx (succDest, succTest)
    let success = ctx.MkImplies (succCond, succSem)

    let failCond = ctx.MkNot succCond
    // In a failure, we have testE!after = destE!before;
    let failDest = makeRel model destE testE
    // and dest!after = dest!before.
    let failTest = makeNoChange model destE
    let failSem = mkAnd2 ctx (succDest, succTest)
    let failure = ctx.MkImplies (failCond, failSem)

    [success
     failure
     // This models set!after = set!before.
     makeNoChange model setE]

/// Emits an arithmetic fetch.
let makeArithFetch model dest src mode =
    let ctx = model.Context

    (* Convert the lvalues to constants.
     * Note that a destination is optional.
     *)
    let destE = Option.map (mkIntLV ctx) dest
    let srcE = mkIntLV ctx src

    (* We have to use Some and List.collect to ensure that the term
     * for dest is only included if there actually _is_ a dest.
     *)
    let terms = [// If dest exists, create dest!after = src!before.
                 Option.map (makeRel model srcE) destE
                 // Create src!after = F(src!before), where F is
                 // defined by the fetch mode.
                 makeFetchUpdate model srcE mode |> Some]
                |> List.choose id

    // The variables whose post-states are bound are src, and, if
    // present, dest.
    let vars = [Option.map flattenLV dest
                Some <| flattenLV src]
               |> List.choose id

    (terms, new Set<string> (vars))

/// Emits a Boolean fetch.
let makeBoolFetch model dest src =
    let ctx = model.Context

    (* As above, but with different types, no modes other than
     * Direct, and a mandatory dest.
     *)
    let destE = mkBoolLV ctx dest
    let srcE = mkBoolLV ctx src

    ( [makeRel model srcE destE
       makeNoChange model srcE],
      new Set<string> ( [flattenLV dest
                         flattenLV src] ))

/// Emits Z3 corresponding to a prim.
/// The result is a pair of the Z3 emission, and the set of names of
/// variables whose post-states are bound by the semantics.
let emitPrim model prim =
    let ctx = model.Context
    match prim with
    | ArithFetch (dest, src, mode) -> makeArithFetch model dest src mode
    | BoolFetch (dest, src) -> makeBoolFetch model dest src
    | ArithCAS (dest, test, set) ->
        (makeCAS model
                 (mkIntLV ctx dest :> Expr)
                 (mkIntLV ctx test :> Expr)
                 set,
         new Set<string> ( [ flattenLV dest
                             flattenLV test ] ))
    | BoolCAS (dest, test, set) ->
        (makeCAS model
                 (mkBoolLV ctx dest :> Expr)
                 (mkBoolLV ctx test :> Expr)
                 set,
         new Set<string> ( [ flattenLV dest
                             flattenLV test ] ))
    | ArithLocalSet (dest, srcE) ->
        (* By the meta-theory, this and BoolLocalSet can be modelled
         * similarly to atomic fetches.
         * However, src is an expression, and (currently) cannot modify
         * dest, so we don't hold it invariant here.
         *)
        let ctx = model.Context
        let destE = mkIntLV ctx dest
        ( [makeRel model srcE destE],
          new Set<string> ( [ flattenLV dest ] ))
    | BoolLocalSet (dest, srcE) ->
        let ctx = model.Context
        let destE = mkBoolLV ctx dest
        ( [makeRel model srcE destE],
          new Set<string> ( [ flattenLV dest ] ))
    | PrimId ->
        ( [ctx.MkTrue ()], Set.empty)
    | PrimAssume (assumption) ->
        // Assumes always only refer to the pre-state.
        ( [subAllInModel model envVarToBefore (assumption :> Expr) :?> BoolExpr],
          Set.empty)
