/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Core.Command

open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model


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
    ///         of primitives represented as <c>VFunc</c>.
    ///     </para>
    /// </summary>
    /// <remarks>
    ///     <para>
    ///         Each <c>VFunc</c> element keys into a <c>Model</c>'s
    ///         <c>Semantics</c> <c>FuncTable</c>.
    ///         This table contains two-state Boolean
    ///         expressions capturing the command's semantics in a
    ///         sort-of-denotational way.
    ///     </para>
    ///     <para>
    ///         Commands are implemented in terms of <c>VFunc</c>s for
    ///         convenience, not because of any deep relationship between
    ///         the two concepts.
    ///     </para>
    /// </remarks>
    type Command = VFunc list

    /// <summary>
    ///     A term over <c>Command</c>s.
    /// </summary>
    /// <typeparam name="wpre">
    ///     The type of the weakest-precondition part of the term.
    /// </typeparam>
    /// <typeparam name="goal">
    ///     The type of the goal part of the term.
    /// </typeparam>
    type PTerm<'wpre, 'goal> = Term<Command, 'wpre, 'goal>


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
    let isNop =
        List.forall
            (fun { Params = ps } ->
                 (* We treat a func as a no-op if all variables it contains
                  * are in the pre-state.  Thus, it cannot be modifying the
                  * post-state, if it is well-formed.
                  *)
                 Seq.forall (function
                             | Typed.Int (AVar (Before _)) -> true
                             | Typed.Int (AVar _) -> false
                             | Typed.Bool (BVar (Before _)) -> true
                             | Typed.Bool (BVar _) -> false
                             | _ -> true)
                            ps)

    /// <summary>
    ///     Active pattern matching assume commands.
    /// </summary>
    let (|Assume|_|) =
        function
        | [ { Name = n ; Params = [ Typed.Bool b ] } ]
          when n = "Assume" -> Some b
        | _ -> None


/// <summary>
///     Pretty printers for commands.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Model.Pretty

    /// Pretty-prints a Command.
    let printCommand = List.map printVFunc >> semiSep

    /// Pretty-prints a PTerm.
    let printPTerm pWPre pGoal = printTerm printCommand pWPre pGoal


/// <summary>
///     Tests for command-related functions.
/// </summary>
module Tests =
    open NUnit.Framework

    /// <summary>
    ///     NUnit tests for command-related functions.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for checking whether a command is a no-op.
        /// </summary>
        static member Nops =
            [ TestCaseData([] : Command)
                .Returns(true)
                .SetName("Classify [] as a no-op")
              TestCaseData([ vfunc "Assume" [ Typed.Bool (bBefore "x") ]])
                .Returns(true)
                .SetName("Classify Assume(x!before) as a no-op")
              TestCaseData([ vfunc "Assume" [ Typed.Bool (bAfter "x") ]])
                .Returns(false)
                .SetName("Reject Assume(x!after) as a no-op")
              TestCaseData([ vfunc "Foo" [ Typed.Int (iBefore "bar")
                                           Typed.Int (iAfter "bar") ]])
                .Returns(false)
                .SetName("Reject Foo(bar!before, bar!after) as a no-op")
              TestCaseData([ vfunc "Foo" [ Typed.Int (iBefore "bar")
                                           Typed.Int (iAfter "bar") ]
                             vfunc "Assume" [ Typed.Bool (bBefore "x") ]])
                .Returns(false)
                .SetName("Reject Foo(bar!before, bar!after); Assume(x!before)\
                          as a no-op") ]

        /// <summary>
        ///     Tests <c>isNop</c>.
        /// </summary>
        [<TestCaseSource("Nops")>]
        member x.``Tests whether isNop correctly identifies no-ops`` c =
            Queries.isNop c

        static member Assumes =
            [ TestCaseData([] : Command)
                .Returns(false)
                .SetName("Reject [] as an assume")
              TestCaseData([ vfunc "Assume" [ Typed.Bool (bBefore "x") ]])
                .Returns(true)
                .SetName("Classify Assume(x!before) as an assume")
              TestCaseData([ vfunc "Foo" [ Typed.Int (iBefore "bar")
                                           Typed.Int (iAfter "bar") ]
                             vfunc "Assume" [ Typed.Bool (bBefore "x") ]])
                .Returns(false)
                .SetName("Reject Foo(bar!before, bar!after); Assume(x!before)\
                          as an assume") ]

        /// <summary>
        ///     Tests <c>Assume</c>.
        /// </summary>
        [<TestCaseSource("Assumes")>]
        member x.``Tests whether Assume correctly identifies assumes`` c =
            match c with
            | Queries.Assume _ -> true
            | _ -> false
