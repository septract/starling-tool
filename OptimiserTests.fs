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
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.View.Traversal
open Starling.Core.Command
open Starling.Core.Sub
open Starling.Optimiser.Graph
open Starling.Optimiser.Term


/// Tests for the term optimiser.
type OptimiserTests() =
    (*
     * Term optimisation
     *)

    /// A test environment of arithmetic after substitutions.
    static member AfterArithSubs =
        [ ("serving", AAdd [siBefore "serving"; AInt 1L])
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
          TestCaseData(BImplies (BGt ((iAfter "s"), (iAfter "t")), BFalse))
            .Returns(BLe ((iAfter "s"), (iAfter "t" )))
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
    open Starling.Core.Sub.Pretty
    open Starling.Optimiser.Pretty

    /// Test after-elimination of Booleans.
    let check expected case : unit =
        let trav =
            boolSubVars
                (tliftToTypedSymVarSrc
                    (afterSubs OptimiserTests.AfterArithSubs OptimiserTests.AfterBoolSubs))
        let result = mapTraversal trav case
        assertOkAndEqual expected result
            (printSubError printTermOptError >> printUnstyled)

    [<Test>]
    let ``Remove arithmetic afters in a simple equality`` () =
        check
            (iEq
                (AAdd [ siBefore "serving"; AInt 1L ] )
                (siBefore "ticket"))
            (iEq (siAfter "serving") (siAfter "ticket"))

    [<Test>]
    let ``Remove arithmetic afters in after-before relation`` () =
        check
            (iEq
                (AAdd [ siBefore "serving"; AInt 1L ] )
                (AAdd [ siBefore "serving"; AInt 1L ] ))
            (iEq
                (siAfter "serving")
                (AAdd [ siBefore "serving"; AInt 1L ] ))

    [<Test>]
    let ``Remove arithmetic afters only if in the environment`` () =
        check
            (BGt (AAdd [ siBefore "serving"; AInt 1L ], siAfter "t"))
            (BGt (siAfter "serving", siAfter "t"))

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
                [ BGt ((AAdd [ siBefore "serving"; AInt 1L ] ), siAfter "t")
                  BOr [ BNot (sbBefore "flag"); sbAfter "pole" ]] )
            (BAnd
                   [ BGt (siAfter "serving", siAfter "t")
                     BOr [ sbAfter "flag"; sbAfter "pole" ]] )

    [<Test>]
    let ``Remove arithmetic afters from a complex expression`` () =
        check
            (BNot
                (BImplies
                    (BNot (sbBefore "flag"),
                    BGt (AAdd [siBefore "serving"; AInt 1L], siAfter "t"))))
            (BNot
                (BImplies
                    (sbAfter "flag",
                    BGt (siAfter "serving", siAfter "t"))))


/// Test cases for substituting afters in a func.
module AfterFuncs =
    open Starling.Utils.Testing
    open Starling.Core.Pretty
    open Starling.Core.Sub.Pretty
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
            (printSubError printTermOptError >> printUnstyled)

    [<Test>]
    let ``Substitute afters in a func with all-after params`` () =
        check
            { Name = "foo"
              Params = [ SMExpr.Int (AAdd [siBefore "serving"; AInt 1L])
                         SMExpr.Bool (BNot (sbBefore "flag")) ] }
            { Name = "foo"
              Params = [ SMExpr.Int (siAfter "serving")
                         SMExpr.Bool (sbAfter "flag") ] }
