/// Types and functions for variables and variable maps.
module Starling.Core.Var

open Chessie.ErrorHandling

open Starling.Collections
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
    ///     A variable reference that may be symbolic.
    ///
    ///     <para>
    ///         A symbolic variable is one whose value depends on an
    ///         uninterpreted function of multiple 'real' Starling variables.
    ///         It allows encoding into Starling of patterns of variable usage
    ///         Starling doesn't yet understand natively.
    ///     </para>
    /// </summary>
    /// <typeparam name="var">
    ///     The non-symbolic variable <c>Sym</c> wraps.
    /// </typeparam>
    type Sym<'var> =
        /// <summary>
        ///     A symbolic variable, predicated over multiple expressions.
        ///     The symbol itself is the name inside the <c>Func</c>.
        /// </summary>
        | Sym of Func<Expr<Sym<'var>>>
        /// <summary>
        ///     A regular, non-symbolic variable.
        | Reg of 'var

    /// <summary>
    ///     An lvalue.
    ///     This is given a separate type in case we add to it later.
    /// </summary>
    type LValue = 
        // TODO(CaptainHayashi): add support for non-variable LValues.
        | LVIdent of string

    /// <summary>
    ///     A formal parameter.
    /// </summary>
    type Param = CTyped<string>

    /// <summary>
    ///     A variable declaration.
    /// </summary>
    type VarDecl = CTyped<string>

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
    ///     An expression of arbitrary type using symbolic <c>Var</c>s.
    /// </summary>
    type SVExpr = Expr<Sym<Var>>
    /// <summary>
    ///     An expression of Boolean type using symbolic <c>Var</c>s.
    /// </summary>
    type SVBoolExpr = BoolExpr<Sym<Var>>
    /// <summary>
    ///     An expression of integral type using <c>Var</c>s.
    /// </summary>
    type SVIntExpr = IntExpr<Sym<Var>>

    /// <summary>
    ///     An expression of arbitrary type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMExpr = Expr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of Boolean type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMBoolExpr = BoolExpr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of integral type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMIntExpr = IntExpr<Sym<MarkedVar>>

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

/// <summary>
///     Pretty printers for variables.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty

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

    /// <summary>
    ///     Pretty-prints a <c>Sym</c>.
    /// </summary>
    /// <param name="pReg">
    ///     Pretty printer to use for regular variables.
    /// </param>
    /// <returns>
    ///     A function taking <c>Sym</c>s and returning pretty-printer
    ///     <c>Command</c>s.
    /// </returns>
    let rec printSym pReg =
        function
        | Sym { Name = sym ; Params = regs } ->
            func (sprintf "%%{%s}" sym) (Seq.map (printExpr (printSym pReg)) regs)
        | Reg reg -> pReg reg

    /// Pretty-prints a VExpr.
    let printVExpr = printExpr String
    /// Pretty-prints a MExpr.
    let printMExpr = printExpr printMarkedVar
    /// Pretty-prints a SVExpr.
    let printSVExpr = printExpr (printSym String)
    /// Pretty-prints a SMExpr.
    let printSMExpr = printExpr (printSym printMarkedVar)
    /// Pretty-prints a VBoolExpr.
    let printVBoolExpr = printBoolExpr String
    /// Pretty-prints a SVBoolExpr.
    let printSVBoolExpr = printBoolExpr (printSym String)
    /// Pretty-prints a SMBoolExpr.
    let printSMBoolExpr = printBoolExpr (printSym printMarkedVar)
    /// Pretty-prints a MBoolExpr.
    let printMBoolExpr = printBoolExpr printMarkedVar
    /// Pretty-prints a MIntExpr.
    let printMIntExpr = printIntExpr printMarkedVar


/// Flattens a LV to a string.
let rec flattenLV = 
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    function 
    | LVIdent s -> s

/// Makes a variable map from a list of type-name pairs.
let makeVarMap lst = 
    lst
    |> List.map valueOf // Extract all names from the list.
    |> findDuplicates
    |> Seq.toList
    |> function
       | [] -> lst
               |> Seq.ofList
               |> Seq.map (fun param -> (valueOf param, typeOf param))
               |> Map.ofSeq |> ok
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
let tryLookupVar
  (env : VarMap)
  : LValue -> CTyped<string> option =
    function 
    | LVIdent s ->
        s
        |> env.TryFind
        |> Option.map (fun ty -> withType ty s)

/// Looks up a variable record in a variable map.
/// Failures are in terms of VarMapError.
let lookupVar
  (env : VarMap)
  (s : LValue)
  : Result<CTyped<string>, VarMapError> =
    s
    |> tryLookupVar env
    |> failIfNone (NotFound (flattenLV s))

(*
 * Expression constructors
 *)

/// Creates an integer sym-variable.
let siVar c = c |> Reg |> AVar

/// Creates an after-marked integer variable.
let iAfter c = c |> After |> AVar

/// Creates an after-marked integer sym-variable.
let siAfter c = c |> After |> Reg |> AVar

/// Creates a before-marked integer variable.
let iBefore c = c |> Before |> AVar

/// Creates an before-marked integer sym-variable.
let siBefore c = c |> Before |> Reg |> AVar

/// Creates a goal-marked integer variable.
let iGoal i c = (i, c) |> Goal |> AVar

/// Creates a goal-marked integer sym-variable.
let siGoal i c = (i, c) |> Goal |> Reg |> AVar

/// Creates an intermediate-marked integer variable.
let iInter i c = (i, c) |> Intermediate |> AVar

/// Creates an intermediate-marked integer sym-variable.
let siInter i c = (i, c) |> Intermediate |> Reg |> AVar

/// Creates a Boolean sym-variable.
let sbVar c = c |> Reg |> BVar

/// Creates an after-marked Boolean variable.
let bAfter c = c |> After |> BVar

/// Creates an before-marked Boolean sym-variable.
let sbAfter c = c |> After |> Reg |> BVar

/// Creates a before-marked Boolean variable.
let bBefore c = c |> Before |> BVar

/// Creates an before-marked Boolean sym-variable.
let sbBefore c = c |> Before |> Reg |> BVar

/// Creates a goal-marked Boolean variable.
let bGoal i c = (i, c) |> Goal |> BVar

/// Creates a goal-marked Inter sym-variable.
let sbGoal i c = (i, c) |> Goal |> Reg |> BVar

/// Creates an intermediate-marked Boolean variable.
let bInter i c = (i, c) |> Intermediate |> BVar

/// Creates an intermediate-marked Boolean sym-variable.
let sbInter i c = (i, c) |> Intermediate |> Reg |> BVar


/// <summary>
///     Extracts all of the regular variables in a symbolic variable.
/// </summary>
/// <param name="sym">
///     The symbolic variable to destructure.
/// </param>
/// <typeparam name="var">
///     The type of regular variables in the symbolic variable.
/// </typeparam>
/// <returns>
///     A list of regular variables bound in a symbolic variable.
/// </returns>
let rec regularVarsInSym
  (sym : Sym<'var>)
  : 'var list =
    match sym with
    | Reg x -> [x]
    | Sym { Params = xs } ->
        xs
        |> List.map (varsIn
                     >> Set.toList
                     >> List.map (valueOf >> regularVarsInSym)
                     >> List.concat)
        |> List.concat



