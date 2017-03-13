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
        /// <summary>A symbolic command.</summary>
        | Symbol of Symbolic<Expr<'RV>>
        /// <summary>An assignment, perhaps nondeterministic.</summary>
        | Assign of lvalue : 'L * rvalue : Expr<'RV> option
        /// <summary>A diverging assertion.</summary>
        | Assume of assumption : BoolExpr<'RV>
        /// <summary>A conditional.</summary>
        | Branch of cond : BoolExpr<'RV>
                  * trueBranch : Microcode<'L, 'RV> list
                  * falseBranch : Microcode<'L, 'RV> list
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
    ///     An intrinsic assignment type.
    /// </summary>
    type AssignType =
        /// <summary>Loading into thread lvalue from shared lvalue.</summary>
        | Load
        /// <summary>Storing into shared lvalue from thread expression.</summary>
        | Store
        /// <summary>Storing into thread lvalue from thread expression.</summary>
        | Local

    /// <summary>
    ///     An intrinsic primitive assignment record.
    /// </summary>
    type Assignment<'Expr> =
        { /// <summary>The type of assignment being done.</summary>
          AssignType : AssignType
          /// <summary>The extended type record of both sides of the assignment.</summary>
          TypeRec : PrimTypeRec
          /// <summary>The lvalue of the assignment.</summary>
          LValue : 'Expr
          /// <summary>The rvalue of the assignment.</summary>
          RValue : 'Expr }

    /// <summary>
    ///     A built-in Starling command.
    ///
    ///     <para>
    ///         Intrinsic commands are basic commands such as assignment that
    ///         need to be handled in a high-level manner.
    ///     </para>
    /// </summary>
    type IntrinsicCommand =
        /// <summary>An atomic integer assign.</summary>
        | IAssign of Assignment<IntExpr<Sym<Var>>>
        /// <summary>An atomic Boolean assign.</summary>
        | BAssign of Assignment<BoolExpr<Sym<Var>>>
        /// <summary>A havoc action.</summary>
        | Havoc of TypedVar

    /// <summary>
    ///     A primitive atomic command.
    /// </summary>
    type PrimCommand =
        /// <summary>An intrinsic command.</summary>
        | Intrinsic of IntrinsicCommand
        /// <summary>A lookup into the model's commands table.</summary>
        | Stored of StoredCommand
        /// <summary>An entirely symbolic command.</summary>
        | SymC of Symbolic<Expr<Sym<Var>>>
        /// <summary>A branching command.</summary>
        | PrimBranch of
            cond : BoolExpr<Sym<Var>>
            * trueBranch : PrimCommand list
            * falseBranch : (PrimCommand list) option
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
          Microcode : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
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
            let result = traverseBoolAsExpr traversal ctx (normalBool s)
            lift (pairMap id swapSemantics) result

/// <summary>
///     Queries on commands.
/// </summary>
module Queries =
    /// <summary>
    ///     Decides whether a primitive command is a no-op.
    /// </summary>
    /// <param name="prim">The prim, as a <c>PrimCmd</c>.</param>
    /// <returns>
    ///     <c>true</c> if the command is a no-op;
    ///     <c>false</c> otherwise.
    /// </returns>
    let rec isNop (prim : PrimCommand) : bool =
        match prim with
        // No Intrinsic commands are no-ops at the moment.
        | Intrinsic _ -> false
        | Stored { Results = ps } -> List.isEmpty ps
        | SymC _ -> false
        | PrimBranch (trueBranch = t; falseBranch = f) ->
            List.forall isNop t && maybe true (List.forall isNop) f
    
    /// <summary>
    ///     Active pattern matching no-operation commands.
    /// </summary>
    let (|NopCmd|_|) : Command -> Command option =
        function
        | c when List.forall isNop c -> Some c
        | _ -> None

    /// <summary>
    ///     If a primitive command is an assume, return its assumption.
    /// </summary>
    /// <param name="prim">The prim, as a <c>PrimCmd</c>.</param>
    /// <returns>
    ///     An option, containing the assumption if
    ///     <paramref name="prim"/> is indeed an assumption.
    /// </returns>
    let assumptionOf (prim : PrimCommand) : BoolExpr<Sym<Var>> option =
        match prim with
        // TODO (CaptainHayashi): more deep analysis here
        | Stored { Name = n; Args = [ Bool (_, e) ] } when n = "Assume" ->
            Some e
        | _ -> None

    /// <summary>
    ///     Decides whether a primitive command is an assume.
    /// </summary>
    /// <param name="prim">The prim, as a <c>PrimCmd</c>.</param>
    /// <returns>
    ///     <c>true</c> if the command is an assume;
    ///     <c>false</c> otherwise.
    /// </returns>
    let isAssume (prim : PrimCommand) : bool =
        match assumptionOf prim with | Some _ -> true | None -> false
 
    /// <summary>
    ///     Active pattern matching assume commands.
    /// </summary>
    let (|Assume|_|) : Command -> SVBoolExpr option =
        function
        | [x] -> assumptionOf x
        | _ -> None

    /// Combines the results of each command into a list of all results
    let commandResults cs =
        let rec primResults prim =
            match prim with
            | Intrinsic (IAssign r) -> [ Expr.Int (r.TypeRec, r.LValue) ]
            | Intrinsic (BAssign r) -> [ Expr.Bool (r.TypeRec, r.LValue) ]
            | Intrinsic (Havoc v) -> [ mkVarExp (mapCTyped Reg v) ]
            | Stored { Results = rs } -> rs
            | SymC _ -> []
            // TODO(MattWindsor91): is this correct?
            | PrimBranch (trueBranch = t; falseBranch = f) ->
                concatMap primResults t
                @ maybe [] (concatMap primResults) f

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
        let argsOnly =
            function
            | SymArg a -> Some a
            | _ -> None

        let rec f prim =
            match prim with
            // TODO(CaptainHayashi): is this sensible!?
            | Stored { Args = xs } -> List.map symExprVars xs
            | SymC s -> List.map symExprVars (List.choose argsOnly s)
            | Intrinsic (IAssign { RValue = y } ) -> [ symExprVars (indefIntExpr y) ]
            | Intrinsic (BAssign { RValue = y } ) -> [ symExprVars (indefBoolExpr y) ]
            | Intrinsic (Havoc _) -> []
            // TODO(CaptainHayashi): is this sensible!?
            | PrimBranch (trueBranch = t; falseBranch = fb) ->
                concatMap f t @ maybe [] (concatMap f) fb

        let vars = collect (concatMap f cmd)
        lift Set.unionMany vars

    /// Determines if some given Command is local with respect to the given
    /// map of thread-local variables
    let isLocalResults (tvars : VarMap) (command : Command) : bool =
        (* We need to see if any of the variables named in the results
           are local.  This can fail, but currently the optimiser can't.
           For now we just assume the command is _not_ local if the
           variable getter failed. *)
        let maybeVars = okOption (commandResultVars command)

        let isVarLocal v =
            maybe false (fun x -> typeOf v = x) (tvars.TryFind (valueOf v))

        maybe false
            (Set.toList >> List.forall isVarLocal)
            maybeVars

    /// <summary>
    ///     Determines whether a command is 'observable' after the effects of
    ///     another command non-atomically sequentially composed after it.
    ///     <para>
    ///         An observable command is one that can diverge, modify shared
    ///         state, or is not referentially transparent, whose assignment
    ///         footprint is not a subset of the other command, or whose
    ///         assignment footprint is not disjoint from the input of the
    ///         other command.
    ///     </para>
    /// <summary>
    /// <param name="tvars">The thread variable map for locality checks.</param>
    /// <param name="c">The command to check for observability.</param>
    /// <param name="d">The command running after <paramref name="c"/>.</param>
    /// <typeparam name="Error">The inner traversal error type.</typeparam>
    /// <returns>
    ///     A Chessie result that is True if <paramref name="c"/> is observable
    ///     after <paramref name="d"/>; false otherwise.
    /// </returns>
    let isObservable
      (tvars : VarMap) (c : Command) (d : Command)
      : Result<bool, TraversalError<'Error>> =
        let cVarsR = commandResultVars c
        let dVarsR = commandResultVars d
        let dArgsR = commandArgs d

        let obsv cVars dArgs dVars =
            let canDiverge =
                // TODO(CaptainHayashi): this is an under-approximation, and
                // possibly even an over-approximation.
                List.exists isAssume c ||
                // TODO(CaptainHayashi): is this even necessary?
                List.exists isAssume d 

            let canModifyShared = not (isLocalResults tvars c)

            // TODO(CaptainHayashi): this is an over-approximation.
            let isSymC = function | SymC _ -> true | _ -> false
            let isReferentiallyOpaque = List.exists isSymC c

            let footprintSubset = Set.isSubset cVars dVars
            let footprintInputDisjoint = Set.isEmpty (Set.intersect cVars dArgs)
            let hasObservableFootprint =
                (not footprintSubset) || (not footprintInputDisjoint)

            canDiverge ||
            canModifyShared ||
            isReferentiallyOpaque || 
            hasObservableFootprint

        lift3 obsv cVarsR dArgsR dVarsR

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

    /// <summary>Pretty-prints an AssignType.</summary>
    let printAssignType (a : AssignType) : Doc =
        String
            (match a with
             | Store -> "store"
             | Load  -> "load"
             | Local -> "local")

    /// <summary>Pretty-prints an IntrinsicCommand.</summary>
    let printIntrinsicCommand (cmd : IntrinsicCommand) : Doc =
        match cmd with
        | BAssign { AssignType = a; TypeRec = ty; LValue = x; RValue = y } ->
            parened <| hsep
                [ String "assign<bool:" <-> printType (Int (ty, ())) <-> String ":" <-> printAssignType a <-> String ">"
                  printBoolExpr (printSym printVar) x
                  printBoolExpr (printSym printVar) y ]
        | IAssign { AssignType = a; TypeRec = ty; LValue = x; RValue = y } ->
            parened <| hsep
                [ String "assign<int:" <-> printType (Int (ty, ())) <-> String ":" <-> printAssignType a <-> String ">"
                  printIntExpr (printSym printVar) x
                  printIntExpr (printSym printVar) y ]
        | Havoc v ->
            parened <| hsep
                [ String "havoc"
                  printTypedVar v ]


    /// Pretty-prints a StoredCommand.
    let printStoredCommand { Name = name; Args = xs; Results = ys } =
        hjoin [ commaSep <| Seq.map (printExpr (printSym printVar)) ys
                " <- " |> String; name |> String; String " "; commaSep <| Seq.map printSVExpr xs ]

    /// Pretty-prints a SymCommand.
    let printSymCommand (sym : Symbolic<Expr<Sym<Var>>>) : Doc =
        // TODO(CaptainHayashi): redundant?
        String "%{"
        <-> printSymbolic (printExpr (printSym printVar)) sym
        <-> String "}"

    /// Pretty-prints a PrimCommand.
    let rec printPrimCommand (prim : PrimCommand) : Doc =
        match prim with
        | Intrinsic s -> printIntrinsicCommand s
        | Stored s -> printStoredCommand s
        | SymC s -> printSymCommand s
        | PrimBranch (cond = c; trueBranch = t; falseBranch = f) ->
            vsep
                [ String "if" <+> printBoolExpr (printSym printVar) c
                  headed "then" (List.map printPrimCommand t)
                  maybe
                    Nop
                    (fun x -> headed "else" (List.map printPrimCommand x))
                    f ]

    /// Pretty-prints a Command.
    let printCommand : Command -> Doc = List.map printPrimCommand >> semiSep

    /// Printing a CommandSemantics prints just the semantic boolexpr associated with it
    let printCommandSemantics pSem sem =
        pSem sem.Semantics

    /// <summary>
    ///     Prints a microcode instruction.
    /// </summary>
    /// <param name="pL">The printer for lvalues.</param>
    /// <param name="pRV">The printer for rvalue variables.</param>
    /// <param name="instr">The instruction to print.</param>
    /// <typeparam name="pL">The type for lvalues.</typeparam>
    /// <typeparam name="pRV">The type for rvalue variables.</typeparam>
    /// <returns>
    ///     The <see cref="Doc"/> representing <paramref name="instr"/>.
    /// </returns>
    let rec printMicrocode
      (pL : 'L -> Doc)
      (pRV : 'RV -> Doc)
      (instr : Microcode<'L, 'RV>)
      : Doc =
        match instr with
        | Symbol sym ->
            String "SYMBOL"
            <+> braced (printSymbolic (printExpr pRV) sym)
        | Assign (lvalue, Some rvalue) ->
            String "ASSIGN" <+> pL lvalue <&> printExpr pRV rvalue
        | Assign (lvalue, None) ->
            String "HAVOC" <+> pL lvalue
        | Assume assumption ->
            String "ASSUME" <+> printBoolExpr pRV assumption
        | Branch (conditional, ifTrue, ifFalse) ->
            vsep
                [ String "IF" <+> printBoolExpr pRV conditional
                  String "THEN"
                  ivsep (List.map (printMicrocode pL pRV) ifTrue)
                  String "ELSE"
                  ivsep (List.map (printMicrocode pL pRV) ifFalse) ]
 
