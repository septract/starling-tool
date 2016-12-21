/// <summary>
///     Tests for the optimiser.
/// </summary>
module Starling.Tests.Optimiser

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.Command
open Starling.Core.Traversal
open Starling.Optimiser.Graph
open Starling.Optimiser.Term


/// Tests for the term optimiser.
type OptimiserTests() =
    (*
     * Term optimisation
     *)

    /// A test environment of arithmetic after substitutions.
    static member AfterArithSubs =
        [ ("serving", IAdd [siBefore "serving"; IInt 1L])
          ("ticket", siBefore "ticket") ]
        |> Map.ofList

    static member AfterBoolSubs =
        [ ("flag", BNot (sbBefore "flag"))
          ("turn", sbBefore "turn") ]
        |> Map.ofList

    /// Test cases for discovering Boolean after-before pairs.
    static member BoolAfterDiscoveries =
        [ TestCaseData(bEq (sbAfter "foo") (sbBefore "foo"))
              .Returns( [ ("foo", sbBefore "foo") ]
                        |> Map.ofList)
              .SetName("Detect a simple Boolean after-before pair")
          TestCaseData(BNot (bEq (sbAfter "foo") (sbBefore "foo")))
              .Returns(Map.empty : Map<string, SMBoolExpr> )
              .SetName("Ignore a negated Boolean after-before pair")
          TestCaseData(BAnd
                           [ bEq (sbAfter "foo") (sbBefore "foo")
                             bEq (sbAfter "bar") (BNot (sbBefore "bar")) ] )
              .Returns( [ ("foo", sbBefore "foo")
                          ("bar", BNot (sbBefore "bar")) ]
                        |> Map.ofList)
              .SetName("Detect a conjunction of Boolean after-before pairs")
          TestCaseData(BOr
                           [ bEq (sbAfter "foo") (sbBefore "foo")
                             bEq (sbAfter "bar") (BNot (sbBefore "bar")) ] )
              .Returns(Map.empty : Map<string, SMBoolExpr> )
              .SetName("Ignore a disjunction of Boolean after-before pairs") ]

    /// Test discovery of Boolean before-after pairs.
    [<TestCaseSource("BoolAfterDiscoveries")>]
    member x.``Boolean before-after pairs should be found correctly`` b =
        b |> findBoolAfters |> Map.ofList

    /// Test cases for simplification.
    static member ObviousBools =
        [ TestCaseData(BNot BFalse : MBoolExpr)
            .Returns(BTrue : MBoolExpr)
            .SetName("Simplify !false as a tautology")
          TestCaseData(BAnd [BTrue; BTrue; BNot BFalse; bEq BFalse BFalse] : MBoolExpr)
            .Returns(BTrue : MBoolExpr)
            .SetName("Simplify true&&true&&!false&&false==false to true")
          TestCaseData(BImplies (BFalse, bEq BTrue BFalse) : MBoolExpr)
            .Returns(BTrue : MBoolExpr)
            .SetName("Simplify false=>true==false to true")
          TestCaseData(BNot BTrue : MBoolExpr)
            .Returns(BFalse : MBoolExpr)
            .SetName("Simplify !true as a contradiction")
          TestCaseData(BAnd [BTrue; BFalse; BNot BFalse; bEq BFalse BFalse] : MBoolExpr)
            .Returns(BFalse : MBoolExpr)
            .SetName("Simplify true&&false&&!false&&false==false to false")
          TestCaseData(BImplies (BTrue, bEq BTrue BFalse) : MBoolExpr)
            .Returns(BFalse : MBoolExpr)
            .SetName("Simplify true=>true==false to false")
          TestCaseData(BImplies ((bAfter "s"), BFalse))
            .Returns(BNot (bAfter "s"))
            .SetName("Simplify =>False into a Negation")
          TestCaseData(BImplies ((bAfter "s"), BTrue))
            .Returns(BTrue : MBoolExpr)
            .SetName("Simplify =>True into a True")
          TestCaseData(BImplies (BGt (normalInt (iAfter "s"), normalInt (iAfter "t")), BFalse))
            .Returns(BLe (normalInt (iAfter "s"), normalInt (iAfter "t" )))
            .SetName("Simplify =>False wrapped around a > into <=")
          TestCaseData(BImplies (BTrue, (bAfter "s")))
            .Returns((bAfter "s"))
            .SetName("Simplify True=>s into s")
          TestCaseData(BImplies (BFalse, (bAfter "s")))
            .Returns(BTrue : MBoolExpr)
            .SetName("Simplify False=>s into True")
            ]

     /// Test Boolean simplification
    [<TestCaseSource("ObviousBools")>]
    member x.``Boolean expressions should be simplified properly`` (b : BoolExpr<MarkedVar>) =
        simp b


/// Test cases for rewriting Boolean expressions containing afters.
module AfterExprs =
    open Starling.Utils.Testing
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty
    open Starling.Optimiser.Pretty

    /// Test after-elimination of Booleans.
    let check expected case : unit =
        let trav =
            tliftToBoolSrc
                (tliftToTypedSymVarSrc
                    (afterSubs OptimiserTests.AfterArithSubs OptimiserTests.AfterBoolSubs))
        let result = mapTraversal trav (normalBool case)
        assertOkAndEqual expected result
            (printTraversalError printTermOptError >> printUnstyled)

    [<Test>]
    let ``Remove arithmetic afters in a simple equality`` () =
        check
            (iEq
                (IAdd [ siBefore "serving"; IInt 1L ] )
                (siBefore "ticket"))
            (iEq (siAfter "serving") (siAfter "ticket"))

    [<Test>]
    let ``Remove arithmetic afters in after-before relation`` () =
        check
            (iEq
                (IAdd [ siBefore "serving"; IInt 1L ] )
                (IAdd [ siBefore "serving"; IInt 1L ] ))
            (iEq
                (siAfter "serving")
                (IAdd [ siBefore "serving"; IInt 1L ] ))

    [<Test>]
    let ``Remove arithmetic afters only if in the environment`` () =
        check
            (BGt (normalInt (IAdd [ siBefore "serving"; IInt 1L ]), normalInt (siAfter "t")))
            (BGt (normalInt (siAfter "serving"), normalInt (siAfter "t")))

    [<Test>]
    let ``Remove Boolean afters in a simple equality`` () =
        check
            (bEq
                (BNot (sbBefore "flag"))
                (sbBefore "turn"))
            (bEq (sbAfter "flag") (sbAfter "turn"))

    [<Test>]
    let ``Remove Boolean afters in after-before relation`` () =
        check
            (bEq (BNot (sbBefore "flag")) (BNot (sbBefore "flag")))
            (bEq (sbAfter "flag") (BNot (sbBefore "flag")))

    [<Test>]
    let ``Remove Boolean afters only if in the environment`` () =
        check
            (BAnd [ BNot (sbBefore "flag"); sbAfter "pole" ])
            (BAnd [ sbAfter "flag"; sbAfter "pole" ] )

    [<Test>]
    let ``Remove afters of both types simultaneously`` () =
        check
            (BAnd
                [ BGt (normalInt (IAdd [ siBefore "serving"; IInt 1L ] ), normalInt (siAfter "t"))
                  BOr [ BNot (sbBefore "flag"); sbAfter "pole" ]] )
            (BAnd
                   [ BGt (normalInt (siAfter "serving"), normalInt (siAfter "t"))
                     BOr [ sbAfter "flag"; sbAfter "pole" ]] )

    [<Test>]
    let ``Remove arithmetic afters from a complex expression`` () =
        check
            (BNot
                (BImplies
                    (BNot (sbBefore "flag"),
                    BGt (normalInt (IAdd [siBefore "serving"; IInt 1L]), normalInt (siAfter "t")))))
            (BNot
                (BImplies
                    (sbAfter "flag",
                    BGt (normalInt (siAfter "serving"), normalInt (siAfter "t")))))


/// Test cases for substituting afters in a func.
module AfterFuncs =
    open Starling.Utils.Testing
    open Starling.Core.Pretty
    open Starling.Core.Traversal.Pretty
    open Starling.Optimiser.Pretty

    /// Test after-elimination of Booleans.
    let check expected case : unit =
        let trav =
            tliftOverFunc
                (tliftToExprSrc
                    (tliftToTypedSymVarSrc
                        (afterSubs OptimiserTests.AfterArithSubs OptimiserTests.AfterBoolSubs)))
        let result = mapTraversal trav case
        assertOkAndEqual expected result
            (printTraversalError printTermOptError >> printUnstyled)

    [<Test>]
    let ``Substitute afters in a func with all-after params`` () =
        check
            { Name = "foo"
              Params = [ normalIntExpr (IAdd [siBefore "serving"; IInt 1L])
                         normalBoolExpr (BNot (sbBefore "flag")) ] }
            { Name = "foo"
              Params = [ normalIntExpr (siAfter "serving")
                         normalBoolExpr (sbAfter "flag") ] }


/// <summary>
///     Test cases for deciding whether to allow graph optimisations.
/// </summary>
module GraphOptGuards =
    open Starling.Core.Graph

    /// A graph consisting of one no-operation cycle.
    let nopCycle =
        { Name = "test"
          Contents =
              Map.ofList
                [ ("x",
                    (Advisory (Multiset.empty),
                     Set.ofList
                        [ { Name = "xloop"; Dest = "x"; Command = [] } ],
                     Set.ofList
                        [ { Name = "xloop"; Src = "x"; Command = [] } ],
                     Normal)
                  ) ] }

    [<Test>]
    let ``nopConnected cannot select the target node`` () =
        Assert.False (nopConnected nopCycle "x" "x")

    [<Test>]
    let ``canCollapseUnobservable cannot collapse {p}nop{p}nop{p}`` () =
        Assert.False (canCollapseUnobservable Map.empty nopCycle "x" [] "x" [] "x")
