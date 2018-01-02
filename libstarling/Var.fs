/// <summary>
///     Types and functions for variables and variable maps.
/// </summary>
module Starling.Core.Var

open Chessie.ErrorHandling

open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr


/// <summary>
///     Types for variables and variable maps.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A variable with no marking.
    /// </summary>
    type Var = string

    /// <summary>
    ///     A variable that has been marked according to whether it comes
    ///     from the pre-state, the post-state, an intermediate state, or
    ///     a possibly-external observation in the goal view.
    /// </summary>
    type MarkedVar =
        /// <summary>
        ///     A variable belonging to the pre-state of a command.
        /// </summary>
        | Before of Var
        /// <summary>
        ///     A variable belonging to the post-state of a command.
        /// </summary>
        | After of Var
        /// <summary>
        ///     A variable belonging to part of the goal term.
        ///     The bigint is used to ensure variables in one goal
        ///     view are separate from variables in another.
        /// </summary>
        | Goal of bigint * Var
        /// <summary>
        ///     A variable belonging to an intermediate state of a composed
        ///     command.
        ///     The bigint is used to ensure different intermediate
        ///     states are separate from each other.
        /// </summary>
        | Intermediate of bigint * Var

    /// <summary>
    ///     A variable reference with an associated type.
    ///     This is usually a formal parameter or variable declaration.
    /// </summary>
    type TypedVar = CTyped<Var>

    /// A variable map.
    type VarMap = Map<string, Type>

    /// <summary>
    ///     A variable scope.
    /// </summary>
    type Scope =
        | /// <summary>Look up variables in thread-local scope.</summary>
          Thread
        | /// <summary>
          ///     Look up variables in shared scope.
          ///     Switch to thread scope for indices, and Any scope for
          ///     symbols.
          /// </summary>
          Shared
        | /// <summary>Look up variables in local first, then shared.</summary>
          Any
        | /// <summary>
          ///     Look up variables in the given local map first, then the next
          ///     scope.
          /// </summary>
          WithMap of map : VarMap * rest : Scope

    /// A mode for the Fetch atomic action.
    type FetchMode =
        | Direct // <a = b>
        | Increment // <a = b++>
        | Decrement // <a = b-->

    /// Represents an error when building or converting a variable map.
    type VarMapError =
        | Duplicate of name : string
        // <summary>A variable is not defined in an environment.</summary>
        | VarNotInEnv
        // <summary>A variable is defined, but in the wrong scope.</summary>
        | VarInWrongScope of expected : Scope * got : Scope


/// <summary>
///     Type synonyms for expressions over various forms of variable.
/// </summary>
[<AutoOpen>]
module VarExprs =
    /// <summary>
    ///     An expression of arbitrary type using <c>Var</c>s.
    /// </summary>
    type VExpr = Expr<Var>
    /// <summary>
    ///     An expression of Boolean type using <c>Var</c>s.
    /// </summary>
    type VBoolExpr = BoolExpr<Var>
    /// <summary>
    ///     An expression of integral type using <c>Var</c>s.
    /// </summary>
    type VIntExpr = IntExpr<Var>

    /// <summary>
    ///     An expression of arbitrary type using <c>MarkedVar</c>s.
    /// </summary>
    type MExpr = Expr<MarkedVar>
    /// <summary>
    ///     An expression of Boolean type using <c>MarkedVar</c>s.
    /// </summary>
    type MBoolExpr = BoolExpr<MarkedVar>
    /// <summary>
    ///     An expression of integral type using <c>MarkedVar</c>s.
    /// </summary>
    type MIntExpr = IntExpr<MarkedVar>

/// <summary>
///     Converts a <c>MarkedVar</c> to a <c>Var</c>, munging its name.
///
///     <para>
///         This function should give each unique <c>MarkedVar</c> a unique
///         name, providing that all are converted with this function.
///         The munging should work with all backends, as it only adds
///         letters and digits to the name.
///     </para>
/// </summary>
let unmarkVar : MarkedVar -> Var =
    function
    | Before c -> sprintf "V%sBEFORE" c
    | After c -> sprintf "V%sAFTER" c
    | Intermediate(i, c) -> sprintf "V%sINT%A" c i
    | Goal(i, c) -> sprintf "V%sGOAL%A" c i


module VarMap =
    /// Makes a variable map from a sequence of typed variables.
    /// Can fail if there are duplicates.
    let ofTypedVarSeq (vars : TypedVar seq) : Result<VarMap, VarMapError> =
        // Before we make the map, make sure we have no duplicates.
        let duplicates = findDuplicates (Seq.map valueOf vars)
        match (Seq.toList duplicates) with
        | [] ->
            let pairs = Seq.map (fun v -> (valueOf v, typeOf v)) vars
            ok (Map.ofSeq pairs)
        | ds -> Bad (List.map Duplicate ds)

    /// Tries to combine two variable maps.
    /// Fails if the environments are not disjoint.
    /// Failures are in terms of VarMapError.
    let combine (a : VarMap) (b : VarMap) : Result<VarMap, VarMapError> =
        Map.fold (fun (sR : Result<VarMap, VarMapError>) name var ->
            trial {
                let! s = sR
                if s.ContainsKey name then return! (fail (Duplicate name))
                else return (s.Add(name, var))
            }) (ok a) b

    /// Tries to look up a variable record in a variable map.
    /// Failures are in terms of Some/None.
    let tryLookup (env : VarMap) (var : Var) : CTyped<string> option =
        Option.map (fun ty -> withType ty var) (env.TryFind var)

    /// <summary>
    ///     Converts a variable map to a sequence of typed variables.
    /// </summary>
    /// <param name="vmap">The map to convert.</param>
    /// <returns>
    ///     <paramref name="vmap"/>, as a sequence of <see cref="TypedVar"/>s.
    /// </returns>
    let toTypedVarSeq (vmap : VarMap) : TypedVar seq =
        Seq.map (fun (name, ty) -> withType ty name) (Map.toSeq vmap)


/// <summary>
///     Module for variable environments.
/// </summary>
module Env =
    /// <summary>
    ///     A Any variable environment.
    /// </summary>
    type Env =
        { /// <summary>The set of thread-local variables.</summary>
          TVars : VarMap
          /// <summary>The set of shared variables.</summary>
          SVars : VarMap }

    /// <summary>
    ///     Creates an <see cref="Env"/>.
    /// </summary>
    /// <param name="tvars">The thread-local variable map.</param>
    /// <param name="svars">The shared variable map.</param>
    /// <returns>An environment with the given variable maps.</returns>
    let env tvars svars = { TVars = tvars; SVars = svars }

    /// <summary>
    ///     Given a scope, return the appropriate scope for indices.
    /// </summary>
    /// <param name="scope">The scope to change for indices.</param>
    /// <returns>The appropriate symbol scope.</returns>
    let rec indexScopeOf (scope : Scope) : Scope =
        match scope with
        | WithMap (map, rest) -> WithMap (map, indexScopeOf rest)
        | x -> Thread

    /// <summary>
    ///     Given a scope, return the appropriate scope for symbolics.
    ///
    ///     <para>
    ///         This function exists because, when processing a shared-scope
    ///         expression and encountering a symbol, we allow thread-local
    ///         variables to appear in the symbol body.
    ///     </para>
    /// </summary>
    /// <param name="scope">The scope to change for symbols.</param>
    /// <returns>The appropriate symbol scope.</returns>
    let rec symbolicScopeOf (scope : Scope) : Scope =
        match scope with
        | WithMap (map, rest) -> WithMap (map, symbolicScopeOf rest)
        | Shared -> Any
        | x -> x

    /// <summary>
    ///     Looks up a variable in an environment.
    /// </summary>
    /// <param name="env">The <see cref="Env"/> to look up.</param>
    /// <param name="scope">The scope at which to look up.</param>
    /// <param name="var">The variable to look up.</param>
    /// <returns>
    ///     A Chessie result in terms of <see cref="VarMapError"/>, containing
    ///     the variable record on success.
    /// </returns>
    let rec lookup (env : Env) (scope : Scope) (var : Var)
      : Result<CTyped<string>, VarMapError> =
        match scope with
        | Thread ->
            match VarMap.tryLookup env.TVars var with
            | Some v -> ok v
            | None ->
                // Look up in shared to give a more detailed error.
                maybe
                    (fail VarNotInEnv)
                    (fun _ ->
                        fail
                            (VarInWrongScope (expected = Thread, got = Shared)))
                    (VarMap.tryLookup env.SVars var)
        | Shared ->
            match VarMap.tryLookup env.SVars var with
            | Some v -> ok v
            | None ->
                // Look up in shared to give a more detailed error.
                maybe
                    (fail VarNotInEnv)
                    (fun _ ->
                        fail
                            (VarInWrongScope (expected = Shared, got = Thread)))
                    (VarMap.tryLookup env.TVars var)
        | Any ->
            (* Currently, the order doesn't matter as both are disjoint.
               However, one day, it might, in which case the thread scope is
               'closer' to program code. *)
            match VarMap.tryLookup env.TVars var with
            | Some v -> ok v
            | None ->
                maybe
                    (fail VarNotInEnv)
                    ok
                    (VarMap.tryLookup env.SVars var)
        | WithMap (map, rest) ->
            match VarMap.tryLookup map var with
            | Some v -> ok v
            | None -> lookup env rest var

    /// <summary>
    ///     Tries to look up a variable in an environment.
    /// </summary>
    /// <param name="env">The <see cref="Env"/> to look up.</param>
    /// <param name="scope">The scope at which to look up.</param>
    /// <param name="var">The variable to look up.</param>
    /// <returns>
    ///     An option, containing the variable record on success.
    /// </returns>
    let tryLookup (env : Env) (scope : Scope) (var : Var)
      : CTyped<string> option =
        okOption (lookup env scope var)


(*
 * Variable constructors
 *)

/// Given a fresh generator, yields a function promoting a string to a
/// goal variable.
let goalVar (fg : FreshGen) = (fg |> getFresh |> curry Goal)

/// Creates a before-marked integer variable.
let iBefore c = c |> Before |> IVar

/// Creates an after-marked integer variable.
let iAfter c = c |> After |> IVar

/// Creates a goal-marked integer variable.
let iGoal i c = (i, c) |> Goal |> IVar

/// Creates an intermediate-marked integer variable.
let iInter i c = (i, c) |> Intermediate |> IVar

/// Creates a before-marked Boolean variable.
let bBefore c = c |> Before |> BVar

/// Creates an after-marked Boolean variable.
let bAfter c = c |> After |> BVar

/// Creates a goal-marked Boolean variable.
let bGoal i c = (i, c) |> Goal |> BVar

/// Creates an intermediate-marked Boolean variable.
let bInter i c = (i, c) |> Intermediate |> BVar


/// <summary>
///     Pretty printers for variables.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.TypeSystem.Pretty

    /// Pretty-prints a lone variable name.
    let printVar : Var -> Doc = String

    /// Pretty-prints a type-name parameter.
    let printTypedVar = printCTyped String

    /// <summary>
    ///     Pretty-prints the name of a variable scope.
    /// </summary>
    /// <param name="scope">The <see cref="Scope"/> to print.</param>
    /// <returns>A <see cref="Doc"/> summarising the scope.</returns>
    let rec printScope (scope : Scope) : Doc =
        match scope with
        // Only signal the presence of an extra map once.
        | WithMap (_, (WithMap (_, s) as wm)) -> printScope wm
        | WithMap (_, r) -> String "local arguments or" <+> printScope r
        | Thread -> String "thread"
        | Shared -> String "shared"
        | Any -> String "thread or shared"

    /// Pretty-prints variable conversion errors.
    let printVarMapError =
        function
        | Duplicate vn ->
            errorStr "Variable"
            <+> quoted (String vn)
            <+> errorStr "is defined multiple times."
        | VarNotInEnv ->
            errorStr "This variable is undefined."
        | VarInWrongScope (expected, got) ->
            let error =
                errorStr "Expected a variable from the"
                <+> errorInfo (printScope expected)
                <+> errorStr "scope, but this variable is in the"
                <+> errorInfo (printScope got)
                <+> errorStr "scope."
            let hint =
                match expected with
                | Thread -> "Consider taking a thread-local copy"
                | Shared -> "Consider using a local command instead."
                | _ -> "No hint available."
            vsep [ error; errorInfoStr hint ]

    /// <summary>
    ///     Pretty-prints a <c>MarkedVar</c>.
    /// </summary>
    let printMarkedVar =
        function
        | Before s -> sexpr "before" String [ s ]
        | After s -> sexpr "after" String [ s ]
        | Intermediate (i, s) -> sexpr "inter" String [ (sprintf "%A" i); s ]
        | Goal (i, s) -> sexpr "goal" String [ (sprintf "%A" i); s ]

    /// Pretty-prints a VExpr.
    let printVExpr = printExpr String
    /// Pretty-prints a MExpr.
    let printMExpr = printExpr printMarkedVar
    /// Pretty-prints a VBoolExpr.
    let printVBoolExpr = printBoolExpr String
    /// Pretty-prints a MBoolExpr.
    let printMBoolExpr = printBoolExpr printMarkedVar
    /// Pretty-prints a MIntExpr.
    let printMIntExpr = printIntExpr printMarkedVar