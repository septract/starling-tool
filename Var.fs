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

    /// A mode for the Fetch atomic action.
    type FetchMode =
        | Direct // <a = b>
        | Increment // <a = b++>
        | Decrement // <a = b-->

    /// Represents an error when building or converting a variable map.
    type VarMapError =
        | Duplicate of name : string
        // The variable was not found.
        | NotFound of name : string


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

// TODO(CaptainHayashi): clean this up?
let varToExpr (v : TypedVar) : Expr<Var> =
    match v with
    | Int iv -> Int (IVar iv)
    | Bool bv -> Bool (BVar bv)
    | Array (eltype, length, av) -> Array (eltype, length, AVar av)

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

    /// Pretty-prints variable conversion errors.
    let printVarMapError =
        function
        | Duplicate vn -> fmt "variable '{0}' is defined multiple times" [ String vn ]
        | NotFound vn -> fmt "variable '{0}' not in environment" [ String vn ]

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

    /// Looks up a variable record in a variable map.
    /// Failures are in terms of VarMapError.
    let lookup (env : VarMap) (var : Var)
      : Result<CTyped<string>, VarMapError> =
        failIfNone (NotFound var) (tryLookup env var)

    /// <summary>
    ///     Converts a variable map to a sequence of typed variables.
    /// </summary>
    /// <param name="vmap">The map to convert.</param>
    /// <returns>
    ///     <paramref name="vmap"/>, as a sequence of <see cref="TypedVar"/>s.
    /// </returns>
    let toTypedVarSeq (vmap : VarMap) : TypedVar seq =
        Seq.map (fun (name, ty) -> withType ty name) (Map.toSeq vmap)


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
///     Tests for <c>Var</c>.
/// </summary>
module Tests =
    open NUnit.Framework

    /// <summary>
    ///     NUnit tests for <c>Var</c>.
    /// </summary>
    type NUnit () =
        /// Test cases for testing goal rewriting.
        static member GoalConstants =
            [ TestCaseData( [ "foo"; "foo"; "foo"] )
                  .Returns( [ Goal (0I, "foo")
                              Goal (1I, "foo")
                              Goal (2I, "foo") ] )
              TestCaseData( ["foo"; "bar"; "baz"] )
                  .Returns( [ Goal (0I, "foo")
                              Goal (1I, "bar")
                              Goal (2I, "baz") ] ) ]

        /// Tests that the frame name generator works fine.
        [<TestCaseSource("GoalConstants")>]
        member x.``goal generation uses fresh variables properly`` xs =
            // TODO(CaptainHayashi): move this to AxiomTests.
            let fg = freshGen ()

            // The fun x boilerplate seems to be necessary.
            // Otherwise, mutations to fg apparently don't propagate!
            List.map (fun x -> goalVar fg x) xs
