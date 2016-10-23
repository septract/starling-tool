/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Core.Command

open Starling.Utils
open Starling.Collections
open Starling.Lang
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic


/// <summary>
///     Types for commands.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A command.
    ///
    ///     <para>
    ///         A command is a list, representing a sequential composition
    ///         of primitives represented as <c>PrimCommand</c>s.
    ///     </para>
    /// </summary>
    /// <remarks>
    ///     <para>
    ///         A PrimCommand is implemented as a triple of a name, the input arguments (the expressions that are evaluated and read)
    ///         and the output results (the variable that are written)
    ///
    ///         for example <x = y++> is translated approximately to { Name = "!ILoad++"; Results = [ siVar "x"; siVar "y" ]; Args = [ siVar "y" ] }
    ///     </para>
    /// </remarks>
    type PrimCommand =
        { Name : string
          Results : TypedVar list
          Args : SMExpr list
          Node : AST.Types.Atomic option }
        override this.ToString() = sprintf "%A" this

    type Command = PrimCommand list

    /// The Semantics of a Command is a pair of the original command and its boolean expr
    type CommandSemantics<'Semantics> =
        { Cmd : Command; Semantics : 'Semantics }
        override this.ToString() = sprintf "%A" this


/// <summary>
///     Queries on commands.
/// </summary>
module Queries =
    /// <summary>
    ///     Decides whether a program command is a no-op.
    /// </summary>
    /// <param name="_arg1">
    ///     The command, as a <c>Command</c>.
    /// </param>
    /// <returns>
    ///     <c>true</c> if the command is a no-op;
    ///     <c>false</c> otherwise.
    /// </returns>
    let isNop : Command -> bool =
        List.forall
            (fun { Results = ps } ->
                  ps = [])

    /// <summary>
    ///     Active pattern matching assume commands.
    /// </summary>
    let (|Assume|_|) : Command -> SMBoolExpr option =
        function
        | [ { Name = n ; Args = [ SMExpr.Bool b ] } ]
          when n = "Assume" -> Some b
        | _ -> None


    /// Combines the results of each command into a list of all results
    let commandResults cs =
        List.fold (fun a c -> a @ c.Results) [] cs

    /// Retrieves the type annotated vars from the arguments to a
    /// command as a list
    let commandArgs cmd =
        let f c = List.map SMExprVars c.Args
        let vars = List.fold (@) [] <| List.map f cmd
        Set.fold (+) Set.empty (Set.ofList vars)

/// <summary>
///     Composition of Boolean expressions representing commands.
/// </summary>
module Compose =
    let maxOpt a b =
        match a, b with
        | Some a, Some b -> Some <| max a b
        | None, Some b -> Some b
        | Some a, None -> Some a
        | None, None -> None


    /// Gets the highest intermediate number for some variable in a given
    /// int expression
    let rec getIntIntermediate v =
        function
        | AVar (Reg (Intermediate (n, x))) when v = x-> Some n
        | AVar (Sym { Params = xs } ) ->
            Seq.fold maxOpt None <| (Seq.map (getIntermediate v) <| xs)
        | AAdd xs | ASub xs | AMul xs ->
            Seq.fold maxOpt None <| (Seq.map (getIntIntermediate v) <| xs)
        | ADiv (x, y) | AMod (x, y) ->
            maxOpt (getIntIntermediate v x) (getIntIntermediate v y)
        | _ -> None

    /// Gets the highest intermediate number for some variable in a given
    /// boolean expression
    and getBoolIntermediate v =
        function
        | BVar (Reg (Intermediate (n, name))) when name = v -> Some n
        | BVar (Sym { Params = xs } ) ->
            Seq.fold maxOpt None <| (Seq.map (getIntermediate v) <| xs)
        | BAnd xs | BOr xs ->
            Seq.fold maxOpt None <| (Seq.map (getBoolIntermediate v) <| xs)
        | BImplies (x, y) ->
            maxOpt (getBoolIntermediate v x) (getBoolIntermediate v y)
        | BNot x -> getBoolIntermediate v x
        | BGt (x, y) | BLt (x, y) | BGe (x, y) | BLe (x, y) ->
            maxOpt (getIntIntermediate v x) (getIntIntermediate v y)
        | BEq (x, y) ->
            maxOpt (getIntermediate v x) (getIntermediate v y)
        | _ -> None

    /// Gets the highest intermediate stage number for a given variable name
    /// in some expression.
    and getIntermediate v =
        function
        | Int x -> getIntIntermediate v x
        | Bool x -> getBoolIntermediate v x

/// <summary>
///     Functions for removing symbols from commands.
///
///     <para>
///         We take the approach that, for a command, whenever we see a
///         statement <c>_ = %{sym}(...)</c> or <c>%{sym}(...) = _</c>,
///         we can drop that statement (leaving the assignment
///         non-deterministic).  This distributes through conjunctions,
///         and the RHS of implications, but not through any other
///         operations.  (It probably can, but for now we're being
///         conservative.)
///     </para>
/// </para>
module SymRemove =
    /// <summary>
    ///     Active pattern matching likely assignments to or from symbols.
    /// </summary>
    let (|SymAssign|_|) : BoolExpr<Sym<'var>>
      -> (Expr<Sym<'var>> * Expr<Sym<'var>>) option =
        // TODO(CaptainHayashi): sound and/or complete?
        function
        | BEq ((Expr.Bool (BVar (Sym _)) as lhs),
               (Expr.Bool _ as rhs))
        | BEq ((Expr.Bool _ as lhs),
               (Expr.Bool (BVar (Sym _)) as rhs))
        | BEq ((Expr.Int (AVar (Sym _)) as lhs),
               (Expr.Int _ as rhs))
        | BEq ((Expr.Int _ as lhs),
               (Expr.Int (AVar (Sym _)) as rhs)) -> Some (lhs, rhs)
        | _ -> None

    /// <summary>
    ///     Tries to remove symbolic assignments from a command in
    ///     Boolean expression form.
    /// </summary>
    let rec removeSym : BoolExpr<Sym<'var>> -> BoolExpr<Sym<'var>> =
        function
        | SymAssign (_, _) -> BTrue
        // Distributivity.
        // TODO(CaptainHayashi): distribute through more things?
        | BAnd xs -> BAnd (List.map removeSym xs)
        | BImplies (lhs, rhs) -> BImplies (lhs, removeSym rhs)
        // Anything else passes through unchanged.
        | x -> x


module Create =
    let command : string -> TypedVar list -> SMExpr list -> PrimCommand =
        fun name results args -> { Name = name; Results = results; Args = args; Node = None }

    let command' : string -> AST.Types.Atomic -> TypedVar list -> SMExpr list -> PrimCommand =
        fun name ast results args -> { Name = name; Results = results; Args = args; Node = Some ast }

/// <summary>
///     Pretty printers for commands.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Symbolic.Pretty

    /// Pretty-prints a Command.
    let printPrimCommand { Name = name; Args = xs; Results = ys } = 
        hjoin [ commaSep <| Seq.map (printCTyped String) ys; " <- " |> String; name |> String; String " "; commaSep <| Seq.map printSMExpr xs ]

    let printCommand : Command -> Doc = List.map printPrimCommand >> semiSep

    /// Printing a CommandSemantics prints just the semantic boolexpr associated with it
    let printCommandSemantics pSem sem =
        pSem sem.Semantics

