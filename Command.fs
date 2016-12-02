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
    ///     Mid-level register transfer logic used to encode Starling
    ///     commands.
    /// </summary>
    /// <typeparam name="L">The type of lvalues.</typeparam>
    /// <typeparam name="RV">The type of rvalue variables.</typeparam>
    type Microcode<'L, 'RV> when 'RV : equality =
        /// <summary>An assignment, perhaps nondeterministic.</summary>
        | Assign of lvalue : 'L * rvalue : Expr<'RV> option
        /// <summary>A diverging assertion.</summary>
        | Assume of assumption : BoolExpr<'RV>
        /// <summary>A conditional.</summary>
        | Branch of conditional : BoolExpr<'RV>
                  * ifTrue : Microcode<'L, 'RV> list
                  * ifFalse : Microcode<'L, 'RV> list
        override this.ToString() = sprintf "%A" this

    /// <summary>
    ///     A reference into the model's atomic commands table.
    /// </summary>
    /// <remarks>
    ///     <para>
    ///         These are implemented as triples of name, input arguments (the expressions that are evaluated and read)
    ///         and output results (the variable that are written)
    ///
    ///         for example <x = y++> is translated approximately to { Name = "!ILoad++"; Results = [ siVar "x"; siVar "y" ]; Args = [ siVar "y" ] }
    ///     </para>
    /// </remarks>
    type StoredCommand =
        { Name : string
          Results : SVExpr list
          Args : SVExpr list
          Node : AST.Types.Atomic option }
        override this.ToString() = sprintf "%A" this

    /// <summary>
    ///     A fully symbolic atomic command.
    ///
    ///     <para>
    ///         A symbolic command has unknown semantics to Starling.  As such,
    ///         we cannot track exactly how it modifies state, and must instead
    ///         take a broad 'working set' of (entire!) variables the command can
    ///         modify (in any way whatsoever).
    ///     </para>
    /// </summary>
    type SymCommand =
        { /// <summary>The symbol representing the command.</summary>
          Symbol : Symbolic<Expr<Sym<Var>>>
          /// <summary>The set of variables this command invalidates.</summary>
          Working : Set<TypedVar> }

    /// <summary>
    ///     A primitive atomic command.
    /// </summary>
    type PrimCommand =
        /// <summary>A lookup into the model's commands table.</summary>
        | Stored of StoredCommand
        /// <summary>An entirely symbolic command.</summary>
        | SymC of SymCommand
        override this.ToString() = sprintf "%A" this

    /// <summary>
    ///     A command.
    ///
    ///     <para>
    ///         A command is a list, representing a sequential composition
    ///         of primitives represented as <c>PrimCommand</c>s.
    ///     </para>
    /// </summary>
    type Command = PrimCommand list

    /// <summary>
    ///     A command, coupled with its various semantic translations.
    /// </summary>
    type CommandSemantics<'Semantics> =
        { /// <summary>The original command.</summary>
          Cmd : Command
          /// <summary>The command's microcode instantiation.</summary>
          Microcode : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list list
          /// <summary>
          ///     The assignment map for the command.
          ///     This maps the post-state of each variable reachable by the
          ///     command to the last assignment made in Microcode for that
          ///     variable.
          /// <summary>
          Assigns : Map<TypedVar, MarkedVar>
          /// <summary>The Boolean translation.</summary>
          Semantics : 'Semantics }
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
    /// <typeparam name="Var">The type of context variables.</typeparam>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let tliftOverCommandSemantics
      (traversal : Traversal<Expr<'SrcVar>, Expr<'DstVar>, 'Error, 'Var>)
      : Traversal<CommandSemantics<BoolExpr<'SrcVar>>,
                  CommandSemantics<BoolExpr<'DstVar>>,
                  'Error, 'Var> =
        fun ctx { Cmd = c; Microcode = m; Assigns = a; Semantics = s } ->
            let swapSemantics s' =
                { Cmd = c; Microcode = m; Assigns = a; Semantics = s' }
            let result = traverseBoolAsExpr traversal ctx (mkTypedSub () s)
            lift (pairMap id swapSemantics) result

/// <summary>
///     Queries on commands.
/// </summary>
module Queries =
    /// <summary>
    ///     Decides whether a program command is a no-op.
    /// </summary>
    /// <param name="command">
    ///     The command, as a <c>Command</c>.
    /// </param>
    /// <returns>
    ///     <c>true</c> if the command is a no-op;
    ///     <c>false</c> otherwise.
    /// </returns>
    let isNop (command : Command) : bool =
        let isPrimNop prim =
            match prim with
            | Stored { Results = ps } -> List.isEmpty ps
            | SymC _ -> false
        List.forall isPrimNop command

    /// <summary>
    ///     Active pattern matching assume commands.
    /// </summary>
    let (|Assume|_|) : Command -> SVBoolExpr option =
        function
        | [ Stored { Name = n ; Args = [ SVExpr.Bool (_, b) ] } ]
          when n = "Assume" -> Some b
        | _ -> None


    /// Combines the results of each command into a list of all results
    let commandResults cs =
        // TODO(CaptainHayashi): are sym working variables really results?
        let primResults prim =
            match prim with
            | Stored { Results = rs } -> rs
            | SymC { Working = ws } ->
                Set.toList (Set.map (mapCTyped Reg >> mkVarExp) ws)

        List.fold (fun a c -> a @ primResults c) [] cs

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
    let commandArgs (cmd : Command) =
        let f prim =
            match prim with
            // TODO(CaptainHayashi): is this sensible!?
            | Stored { Args = xs }
            | SymC { Symbol = { Args = xs } } -> List.map symExprVars xs
        let vars = collect (concatMap f cmd)
        lift Set.unionMany vars

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
    let rec getIntIntermediate
      (var : Var) (expr : IntExpr<Sym<MarkedVar>>) : bigint option =
        match expr with
        | IVar (Reg (Intermediate (n, x))) when var = x -> Some n
        | IVar (Sym { Args = xs } ) ->
            Seq.fold maxOpt None (Seq.map (getIntermediate var) xs)
        | IAdd xs | ISub xs | IMul xs ->
            Seq.fold maxOpt None (Seq.map (getIntIntermediate var) xs)
        | IDiv (x, y) | IMod (x, y) ->
            maxOpt (getIntIntermediate var x) (getIntIntermediate var y)
        // TODO(CaptainHayashi): need to convince myself this is correct.
        | IIdx (arr, idx) ->
            maxOpt
                (getArrayIntermediate var (stripTypeRec arr))
                (getIntIntermediate var (stripTypeRec idx))
        | _ -> None

    /// Gets the highest intermediate number for some variable in a given
    /// boolean expression
    and getBoolIntermediate
      (var : Var) (expr : BoolExpr<Sym<MarkedVar>>) : bigint option =
        match expr with
        | BVar (Reg (Intermediate (n, name))) when name = var -> Some n
        | BVar (Sym { Args = xs } ) ->
            Seq.fold maxOpt None (Seq.map (getIntermediate var) xs)
        | BAnd xs | BOr xs ->
            Seq.fold maxOpt None (Seq.map (getBoolIntermediate var) xs)
        | BImplies (x, y) ->
            maxOpt (getBoolIntermediate var x) (getBoolIntermediate var y)
        | BNot x -> getBoolIntermediate var x
        | BGt (x, y) | BLt (x, y) | BGe (x, y) | BLe (x, y) ->
            maxOpt
                (getIntIntermediate var (stripTypeRec x))
                (getIntIntermediate var (stripTypeRec y))
        | BEq (x, y) ->
            maxOpt (getIntermediate var x) (getIntermediate var y)
        // TODO(CaptainHayashi): need to convince myself this is correct.
        | BIdx (arr, idx) ->
            maxOpt
                (getArrayIntermediate var (stripTypeRec arr))
                (getIntIntermediate var (stripTypeRec idx))
        | _ -> None

    /// Gets the highest intermediate number for some variable in a given
    /// array expression
    and getArrayIntermediate
      (var : Var) (expr : ArrayExpr<Sym<MarkedVar>>) : bigint option =
        match expr with
        | AVar (Reg (Intermediate (n, name))) when name = var -> Some n
        | AVar (Sym { Args = xs } ) ->
            Seq.fold maxOpt None (Seq.map (getIntermediate var) xs)
        // TODO(CaptainHayashi): need to convince myself this is correct.
        | AIdx (arr, idx) ->
            maxOpt
                (getArrayIntermediate var (stripTypeRec arr))
                (getIntIntermediate var (stripTypeRec idx))
        | AVar _ -> None
        | AUpd (arr, idx, upd) ->
            maxOpt
                (getArrayIntermediate var arr)
                (maxOpt
                    (getIntIntermediate var (stripTypeRec idx))
                    (getIntermediate var upd))

    /// Gets the highest intermediate stage number for a given variable name
    /// in some expression.
    and getIntermediate
      (var : Var) (expr : Expr<Sym<MarkedVar>>) : bigint option =
        match expr with
        | Int (_, x) -> getIntIntermediate var x
        | Bool (_, x) -> getBoolIntermediate var x
        | Array (_, x) -> getArrayIntermediate var x

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
        | BEq ((Expr.Bool (_, BVar (Sym _)) as lhs),
               (Expr.Bool _ as rhs))
        | BEq ((Expr.Bool _ as lhs),
               (Expr.Bool (_, BVar (Sym _)) as rhs))
        | BEq ((Expr.Int (_, IVar (Sym _)) as lhs),
               (Expr.Int _ as rhs))
        | BEq ((Expr.Int _ as lhs),
               (Expr.Int (_, IVar (Sym _)) as rhs)) -> Some (lhs, rhs)
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
        Stored { Name = name; Results = results; Args = args; Node = None }

    let command' (name : string) (ast : AST.Types.Atomic) (results : SVExpr list) (args : SVExpr list) : PrimCommand =
        Stored { Name = name; Results = results; Args = args; Node = Some ast }

/// <summary>
///     Pretty printers for commands.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Symbolic.Pretty

    /// Pretty-prints a StoredCommand.
    let printStoredCommand { Name = name; Args = xs; Results = ys } =
        hjoin [ commaSep <| Seq.map (printExpr (printSym printVar)) ys
                " <- " |> String; name |> String; String " "; commaSep <| Seq.map printSVExpr xs ]

    /// Pretty-prints a SymCommand.
    let printSymCommand { Symbol = sym; Working = wk } : Doc =
        commaSep (Seq.map printTypedVar wk)
        <+> String "<-%{"
        <-> printInterpolatedSymbolicSentence (printExpr (printSym printVar)) sym.Sentence sym.Args
        <-> String "}"

    /// Pretty-prints a PrimCommand.
    let printPrimCommand (prim : PrimCommand) : Doc =
        match prim with
        | Stored s -> printStoredCommand s
        | SymC s -> printSymCommand s

    /// Pretty-prints a Command.
    let printCommand : Command -> Doc = List.map printPrimCommand >> semiSep

    /// Printing a CommandSemantics prints just the semantic boolexpr associated with it
    let printCommandSemantics pSem sem =
        pSem sem.Semantics
