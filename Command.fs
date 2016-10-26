/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Core.Command

open Chessie.ErrorHandling

open Starling.Utils
open Starling.Collections
open Starling.Lang
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Traversal


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
          Results : SVExpr list
          Args : SVExpr list
          Node : AST.Types.Atomic option }
        override this.ToString() = sprintf "%A" this

    type Command = PrimCommand list

    /// The Semantics of a Command is a pair of the original command and its boolean expr
    type CommandSemantics<'Semantics> =
        { Cmd : Command; Semantics : 'Semantics }
        override this.ToString() = sprintf "%A" this

/// <summary>
///     Traversals on commands.
/// </summary>
module Traversal =
    open Starling.Core.Traversal

    /// <summary>
    ///     Lifts a <c>Traversal</c> over all expressions in a
    ///     <see cref="CommandSemantics"/>.
    /// </summary>
    /// <param name="traversal">
    ///     The <c>Traversal</c> to map over all expressions in the command.
    ///     This should map from expressions to expressions.
    /// </param>
    /// <typeparam name="SrcVar">
    ///     The type of variables before traversal.
    /// </typeparam>
    /// <typeparam name="DstVar">
    ///     The type of variables after traversal.
    /// </typeparam>
    /// <typeparam name="Error">
    ///     The type of any returned errors.
    /// </typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverCommandSemantics
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error>)
      : Traversal<CommandSemantics<BoolExpr<'SrcVar>>,
                  CommandSemantics<BoolExpr<'DstVar>>,
                  'Error> =
        fun ctx { Cmd = c; Semantics = s } ->
            let swapSemantics s' = { Cmd = c; Semantics = s' }
            let result = traverseBoolAsExpr traversal ctx s
            lift (pairMap id swapSemantics) result

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
        List.forall (fun { Results = ps } -> List.isEmpty ps )

    /// <summary>
    ///     Active pattern matching assume commands.
    /// </summary>
    let (|Assume|_|) : Command -> SVBoolExpr option =
        function
        | [ { Name = n ; Args = [ SVExpr.Bool b ] } ]
          when n = "Assume" -> Some b
        | _ -> None


    /// Combines the results of each command into a list of all results
    let commandResults cs =
        List.fold (fun a c -> a @ c.Results) [] cs

    /// <summary>
    ///     Gets all variables mentioned in the results of a command.
    /// </summary>
    /// <param name="cmd">The <see cref="Command"/> to query.</param>
    /// <typeparam name="'Error">The traversal-internal error type.</typeparam>
    /// <returns>
    ///     All variables mentioned in <paramref name="cmd"/>'s results, as
    ///     <see cref="TypedVar"/>s.  This is wrapped in a result, because the
    ///     internal traversal can fail.
    /// </returns>
    let commandResultVars (cmd : Command)
      : Result<Set<TypedVar>, TraversalError<'Error>> =
        let results = commandResults cmd
        let trav = tchainL (tliftOverExpr collectSymVars) id
        findVars trav results

    /// Retrieves the type annotated vars from the arguments to a
    /// command as a list
    let commandArgs cmd =
        let f c = List.map SVExprVars c.Args
        let vars = collect (concatMap f cmd)
        lift Set.unionMany vars

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
        | IVar (Reg (Intermediate (n, _))) -> n + 1I
        | IVar (Sym { Params = xs } ) ->
            xs |> Seq.map nextIntermediate |> Seq.fold (curry bigint.Max) 0I
        | IVar _ | IInt _ -> 0I
        | IAdd xs | ISub xs | IMul xs ->
            xs |> Seq.map nextIntIntermediate |> Seq.fold (curry bigint.Max) 0I
        | IDiv (x, y) ->
            bigint.Max (nextIntIntermediate x, nextIntIntermediate y)
        // Is this correct?
        | IIdx (_, _, arr, idx) ->
            bigint.Max (nextArrayIntermediate arr, nextIntIntermediate idx)

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
        | IVar (Reg (Intermediate (n, x))) when v = x-> Some n
        | IVar (Sym { Params = xs } ) ->
            Seq.fold maxOpt None <| (Seq.map (getIntermediate v) <| xs)
        | IVar _ | IInt _ -> None
        | IAdd xs | ISub xs | IMul xs ->
            Seq.fold maxOpt None <| (Seq.map (getIntIntermediate v) <| xs)
        | IDiv (x, y) ->
            maxOpt (getIntIntermediate v x) (getIntIntermediate v y)
        // Is this correct?
        | IIdx (_, _, arr, idx) ->
            maxOpt (getArrayIntermediate v arr) (getIntIntermediate v idx)
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
        // Is this correct?
        | BIdx (_, _, arr, idx) ->
            bigint.Max (nextArrayIntermediate arr, nextIntIntermediate idx)

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
        // Is this correct?
        | BIdx (_, _, arr, idx) ->
            maxOpt (getArrayIntermediate v arr) (getIntIntermediate v idx)
        | _ -> None

    /// <summary>
    ///     Finds the highest intermediate stage number in an array
    ///     expression.
    ///     Returns one higher.
    /// </summary>
    /// <param name="_arg1">
    ///     The <c>ArrayExpr</c> to investigate.
    /// </param>
    /// <returns>
    ///     The next available intermediate stage number.
    ///     If the expression has no intermediate stages, we return 0.
    /// </returns>
    and nextArrayIntermediate : ArrayExpr<Sym<_>> -> bigint =
        function
        | AVar (Reg (Intermediate (n, _))) -> n + 1I
        | AVar (Sym { Params = xs } ) ->
            xs |> Seq.map nextIntermediate |> Seq.fold (curry bigint.Max) 0I
        | AVar _ -> 0I
        // TODO(CaptainHayashi): is this correct?
        | AIdx (_, _, arr, idx) ->
            bigint.Max (nextArrayIntermediate arr, nextIntIntermediate idx)
        | AUpd (_, _, arr, idx, upd) ->
            bigint.Max
                (nextArrayIntermediate arr,
                 bigint.Max(nextIntIntermediate idx, nextIntermediate upd))

    /// Gets the highest intermediate number for some variable in a given
    /// array expression
    and getArrayIntermediate v =
        function
        | AVar (Reg (Intermediate (n, name))) when name = v -> Some n
        | AVar (Sym { Params = xs } ) ->
            Seq.fold maxOpt None <| (Seq.map (getIntermediate v) <| xs)
        // Is this correct?
        | AIdx (_, _, arr, idx) ->
            maxOpt (getArrayIntermediate v arr) (getIntIntermediate v idx)
        | AVar _ -> None
        | AUpd (_, _, arr, idx, upd) ->
            maxOpt
                (getArrayIntermediate v arr)
                (maxOpt (getIntIntermediate v idx) (getIntermediate v upd))

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
        | Array (_, _, x) -> nextArrayIntermediate x

    /// Gets the highest intermediate stage number for a given variable name
    /// in some expression.
    and getIntermediate v =
        function
        | Int x -> getIntIntermediate v x
        | Bool x -> getBoolIntermediate v x
        | Array (_, _, x) -> getArrayIntermediate v x


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
        | BEq ((Expr.Int (IVar (Sym _)) as lhs),
               (Expr.Int _ as rhs))
        | BEq ((Expr.Int _ as lhs),
               (Expr.Int (IVar (Sym _)) as rhs)) -> Some (lhs, rhs)
        | _ -> None

    /// <summary>
    ///     Tries to remove symbolic assignments from a command in
    ///     Boolean expression form.
    /// </summary>
    let rec removeSym : BoolExpr<Sym<'var>> -> BoolExpr<Sym<'var>> =
        function
        | SymAssign _ -> BTrue
        // Distributivity.
        // TODO(CaptainHayashi): distribute through more things?
        | BAnd xs -> BAnd (List.map removeSym xs)
        | BImplies (lhs, rhs) -> BImplies (lhs, removeSym rhs)
        // Anything else passes through unchanged.
        | x -> x


module Create =
    let command (name : string) (results : SVExpr list) (args : SVExpr list) : PrimCommand =
        { Name = name; Results = results; Args = args; Node = None }

    let command' (name : string) (ast : AST.Types.Atomic) (results : SVExpr list) (args : SVExpr list) : PrimCommand =
        { Name = name; Results = results; Args = args; Node = Some ast }

/// <summary>
///     Pretty printers for commands.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Symbolic.Pretty

    /// Pretty-prints a Command.
    let printPrimCommand { Name = name; Args = xs; Results = ys } =
        hjoin [ commaSep <| Seq.map (printExpr (printSym printVar)) ys
                " <- " |> String; name |> String; String " "; commaSep <| Seq.map printSVExpr xs ]

    let printCommand : Command -> Doc = List.map printPrimCommand >> semiSep

    /// Printing a CommandSemantics prints just the semantic boolexpr associated with it
    let printCommandSemantics pSem sem =
        pSem sem.Semantics
