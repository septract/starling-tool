/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Core.Command

open Starling.Utils
open Starling.Collections
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
    type PrimCommand = { Name : string; Results : TypedVar list; Args : SMExpr list }
    type Command = PrimCommand list

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
    let (|Assume|_|) =
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
    /// <summary>
    ///     Finds the highest intermediate stage number in an integral
    ///     expression.
    ///     Returns one higher.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>IntExpr</c> to investigate.
    /// </param>
    /// <returns>
    ///     The next available intermediate stage number.
    ///     If the expression has no intermediate stages, we return 0.
    /// </returns>
    let rec nextIntIntermediate : IntExpr<Sym<_>> -> bigint =
        function
        | AVar (Reg (Intermediate (n, _))) -> n + 1I
        | AVar (Sym { Params = xs } ) ->
            xs |> Seq.map nextIntermediate |> Seq.fold (curry bigint.Max) 0I
        | AVar _ | AInt _ -> 0I
        | AAdd xs | ASub xs | AMul xs ->
            xs |> Seq.map nextIntIntermediate |> Seq.fold (curry bigint.Max) 0I
        | ADiv (x, y) ->
            bigint.Max (nextIntIntermediate x, nextIntIntermediate y)

    and maxOpt a b =
        match a, b with
        | Some a, Some b -> Some <| max a b
        | None, Some b -> Some b
        | Some a, None -> Some a
        | None, None -> None


    /// Gets the highest intermediate number for some variable in a given
    /// int expression
    and getIntIntermediate v =
        function
        | AVar (Reg (Intermediate (n, x))) when v = x-> Some n
        | AVar (Sym { Params = xs } ) ->
            Seq.fold maxOpt None <| (Seq.map (getIntermediate v) <| xs)
        | AVar _ | AInt _ -> None
        | AAdd xs | ASub xs | AMul xs ->
            Seq.fold maxOpt None <| (Seq.map (getIntIntermediate v) <| xs)
        | ADiv (x, y) ->
            maxOpt (getIntIntermediate v x) (getIntIntermediate v y)
        | _ -> None

    /// <summary>
    ///     Finds the highest intermediate stage number in a Boolean expression.
    ///     Returns one higher.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>BoolExpr</c> to investigate.
    /// </param>
    /// <returns>
    ///     The next available intermediate stage number.
    ///     If the expression has no intermediate stages, we return 0.
    /// </returns>
    and nextBoolIntermediate : BoolExpr<Sym<_>> -> bigint =
        function
        | BVar (Reg (Intermediate (n, _))) -> n + 1I
        | BVar (Sym { Params = xs } ) ->
            xs |> Seq.map nextIntermediate |> Seq.fold (curry bigint.Max) 0I
        | BVar _ -> 0I
        | BAnd xs | BOr xs ->
            xs |> Seq.map nextBoolIntermediate |> Seq.fold (curry bigint.Max) 0I
        | BImplies (x, y) ->
            bigint.Max (nextBoolIntermediate x, nextBoolIntermediate y)
        | BNot x -> nextBoolIntermediate x
        | BGt (x, y) | BLt (x, y) | BGe (x, y) | BLe (x, y) ->
            bigint.Max (nextIntIntermediate x, nextIntIntermediate y)
        | BEq (x, y) ->
            bigint.Max (nextIntermediate x, nextIntermediate y)
        | BTrue | BFalse -> 0I

    /// Gets the highest intermediate number for some variable in a given
    /// boolean expression
    and getBoolIntermediate v =
        function
        | BVar (Reg (Intermediate (n, name))) when name = v -> Some n
        | BVar (Sym { Params = xs } ) ->
            Seq.fold maxOpt None <| (Seq.map (getIntermediate v) <| xs)
        | BVar (Reg (After x)) when x = v -> None
        | BVar (Reg (Before x)) when x = v -> None
        | BVar (Reg (Intermediate(i, x))) when x = v -> Some i
        | BAnd xs | BOr xs ->
            Seq.fold maxOpt None <| (Seq.map (getBoolIntermediate v) <| xs)
        | BImplies (x, y) ->
            maxOpt (getBoolIntermediate v x) (getBoolIntermediate v y)
        | BNot x -> getBoolIntermediate v x
        | BGt (x, y) | BLt (x, y) | BGe (x, y) | BLe (x, y) ->
            maxOpt (getIntIntermediate v x) (getIntIntermediate v y)
        | BEq (x, y) ->
            maxOpt (getIntermediate v x) (getIntermediate v y)
        | BTrue | BFalse -> None
        | _ -> None

    /// <summary>
    ///     Finds the highest intermediate stage number in an expression.
    ///     Returns one higher.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>Expr</c> to investigate.
    /// </param>
    /// <returns>
    ///     The next available intermediate stage number.
    ///     If the expression has no intermediate stages, we return 0.
    /// </returns>
    and nextIntermediate : Expr<Sym<_>> -> bigint =
        function
        | Int x -> nextIntIntermediate x
        | Bool x -> nextBoolIntermediate x

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
    let (|SymAssign|_|) =
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
    let rec removeSym : BoolExpr<Sym<'a>> -> BoolExpr<Sym<'a>> =
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
        fun name results args -> { Name = name; Results = results; Args = args }

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
