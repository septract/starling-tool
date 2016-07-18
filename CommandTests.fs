/// <summary>
///     Functions and types for commands.
/// </summary>
module Starling.Tests.Core.Command

open Starling.Core.TypeSystem
open Starling.Core

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
            [ TestCaseData([] : Command.Types.Command)
                .Returns(true)
                .SetName("Classify [] as a no-op")
              TestCaseData([ Model.smvfunc "Assume" [ Symbolic.SymExprs.SMExpr.Bool (Symbolic.Create.sbBefore "x") ]])
                .Returns(true)
                .SetName("Classify Assume(x!before) as a no-op")
              TestCaseData([ Model.smvfunc "Assume"
                                 [ Symbolic.SymExprs.SMExpr.Bool (Symbolic.Create.sbAfter "x") ]])
                .Returns(false)
                .SetName("Reject Assume(x!after) as a no-op")
              TestCaseData([ Model.smvfunc "Foo"
                                 [ Symbolic.SymExprs.SMExpr.Int (Symbolic.Create.siBefore "bar")
                                   Symbolic.SymExprs.SMExpr.Int (Symbolic.Create.siAfter "bar") ]])
                .Returns(false)
                .SetName("Reject Foo(bar!before, bar!after) as a no-op")
              TestCaseData([ Model.smvfunc "Foo"
                                 [ Symbolic.SymExprs.SMExpr.Int (Symbolic.Create.siBefore "bar")
                                   Symbolic.SymExprs.SMExpr.Int (Symbolic.Create.siAfter "bar") ]
                             Model.smvfunc "Assume"
                                 [ Symbolic.SymExprs.SMExpr.Bool (Symbolic.Create.sbBefore "x") ]])
                .Returns(false)
                .SetName("Reject Foo(bar!before, bar!after); Assume(x!before)\
                          as a no-op") ]

        /// <summary>
        ///     Tests <c>isNop</c>.
        /// </summary>
        [<TestCaseSource("Nops")>]
        member x.``Tests whether isNop correctly identifies no-ops`` c =
            Command.Queries.isNop c

        static member Assumes =
            [ TestCaseData([] : Command.Types.Command)
                .Returns(false)
                .SetName("Reject [] as an assume")
              TestCaseData([ Model.smvfunc "Assume"
                                 [ Symbolic.SymExprs.SMExpr.Bool (Symbolic.Create.sbBefore "x") ]])
                .Returns(true)
                .SetName("Classify Assume(x!before) as an assume")
              TestCaseData([ Model.smvfunc "Foo"
                                 [ Symbolic.SymExprs.SMExpr.Int (Symbolic.Create.siBefore "bar")
                                   Symbolic.SymExprs.SMExpr.Int (Symbolic.Create.siAfter "bar") ]
                             Model.smvfunc "Assume" [ Symbolic.SymExprs.SMExpr.Bool (Symbolic.Create.sbBefore "x") ]])
                .Returns(false)
                .SetName("Reject Foo(bar!before, bar!after); Assume(x!before)\
                          as an assume") ]

        /// <summary>
        ///     Tests <c>Assume</c>.
        /// </summary>
        [<TestCaseSource("Assumes")>]
        member x.``Tests whether Assume correctly identifies assumes`` c =
            match c with
            | Command.Queries.Assume _ -> true
            | _ -> false

        /// Test cases for intermediate finding.
        static member NextIntermediates =
            [ TestCaseData(Symbolic.SymExprs.SMExpr.Bool (Symbolic.Create.sbInter 5I "foo"))
                .Returns(6I)
                .SetName("nextIntermediate on Bool intermediate is one higher")
              TestCaseData(Symbolic.SymExprs.SMExpr.Bool (Expr.Types.BNot (Symbolic.Create.sbInter 10I "bar")))
                .Returns(11I)
                .SetName("nextIntermediate on 'not' passes through")
              TestCaseData(Symbolic.SymExprs.SMExpr.Bool (Expr.Types.BImplies (Symbolic.Create.sbInter 6I "a", Symbolic.Create.sbInter 11I "b")))
                .Returns(12I)
                .SetName("nextIntermediate on 'implies' is one higher than max")
              TestCaseData(Symbolic.SymExprs.SMExpr.Int
                               (Expr.Types.AAdd [ Symbolic.Create.siInter 1I "a";
                                       Symbolic.Create.siAfter "b";
                                       Symbolic.Create.siBefore "c";
                                       Symbolic.Create.siInter 2I "d"; ] ))
                .Returns(3I)
                .SetName("nextIntermediate on 'add' is one higher than max") ]

        /// Tests whether nextIntermediate works.
        [<TestCaseSource("NextIntermediates")>]
        member x.``test whether nextIntermediate gets the correct level`` expr =
            Command.Compose.nextIntermediate expr
