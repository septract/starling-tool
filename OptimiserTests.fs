module Starling.Tests.Optimiser

open NUnit.Framework
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
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
        [ ("serving", AAdd [iBefore "serving"; AInt 1L])
          ("ticket", iBefore "ticket") ]
        |> Map.ofList

    static member AfterBoolSubs =
        [ ("flag", BNot (bBefore "flag"))
          ("turn", bBefore "turn") ]
        |> Map.ofList

    /// Test cases for rewriting Boolean expressions containing afters.
    static member AfterBools =
        [ TestCaseData(iEq (iAfter "serving") (iAfter "ticket"))
            .Returns(iEq (AAdd [iBefore "serving"; AInt 1L])
                         (iBefore "ticket"))
            .SetName("Remove arithmetic afters in a simple equality")
          TestCaseData(iEq (iAfter "serving") (AAdd [iBefore "serving"
                                                     AInt 1L]))
            .Returns(iEq (AAdd [iBefore "serving"; AInt 1L])
                         (AAdd [iBefore "serving"; AInt 1L]))
            .SetName("Remove arithmetic afters in after-before relation")
          TestCaseData(BGt (iAfter "serving", iAfter "t"))
            .Returns(BGt (AAdd [iBefore "serving"; AInt 1L],
                          iAfter "t"))
            .SetName("Remove arithmetic afters only if in the environment")
          TestCaseData(bEq (bAfter "flag") (bAfter "turn"))
            .Returns(bEq (BNot (bBefore "flag"))
                         (bBefore "turn"))
            .SetName("Remove Boolean afters in a simple equality")
          TestCaseData(bEq (bAfter "flag") (BNot (bBefore "flag")))
            .Returns(bEq (BNot (bBefore "flag"))
                         (BNot (bBefore "flag")))
            .SetName("Remove Boolean afters in after-before relation")
          TestCaseData(BAnd [bAfter "flag"; bAfter "pole"])
            .Returns(BAnd [ BNot (bBefore "flag")
                            bAfter "pole" ])
            .SetName("Remove Boolean afters only if in the environment")
          TestCaseData(BAnd [BGt (iAfter "serving", iAfter "t")
                             BOr [bAfter "flag"; bAfter "pole"]])
            .Returns(BAnd [ BGt ((AAdd [iBefore "serving"
                                        AInt 1L]), iAfter "t")
                            BOr [BNot (bBefore "flag"); bAfter "pole" ]])
            .SetName("Remove afters of both types simultaneously")
          TestCaseData(BNot (BImplies (bAfter "flag", BGt (iAfter "serving",
                                                           iAfter "t"))))
            .Returns(BNot (BImplies (BNot (bBefore "flag"),
                                     BGt (AAdd [iBefore "serving"; AInt 1L],
                                          iAfter "t"))))
            .SetName("Remove arithmetic afters from a complex expression")]

    /// Test after-elimination of Booleans.
    [<TestCaseSource("AfterBools")>]
    member x.``After-elimination of Booleans should operate correctly`` b =
        TypeMapper.mapBool
            (afterSubs OptimiserTests.AfterArithSubs OptimiserTests.AfterBoolSubs)
            b

    /// Test cases for discovering Boolean after-before pairs.
    static member BoolAfterDiscoveries =
        let me : Map<string, MBoolExpr> = Map.empty
        [ TestCaseData(bEq (bAfter "foo") (bBefore "foo"))
            .Returns(
                [("foo", bBefore "foo")]
                |> Map.ofList)
            .SetName("Detect a simple Boolean after-before pair")
          TestCaseData(BNot (bEq (bAfter "foo") (bBefore "foo")))
            .Returns(me)
            .SetName("Ignore a negated Boolean after-before pair")
          TestCaseData(BAnd [bEq (bAfter "foo") (bBefore "foo")
                             bEq (bAfter "bar") (BNot (bBefore "bar"))])
            .Returns(
                [("foo", bBefore "foo")
                 ("bar", BNot (bBefore "bar"))]
                |> Map.ofList)
            .SetName("Detect a conjunction of Boolean after-before pairs")
          TestCaseData(BOr [bEq (bAfter "foo") (bBefore "foo")
                            bEq (bAfter "bar") (BNot (bBefore "bar"))])
            .Returns(me)
            .SetName("Ignore a disjunction of Boolean after-before pairs") ]

    /// Test discovery of Boolean before-after pairs.
    [<TestCaseSource("BoolAfterDiscoveries")>]
    member x.``Boolean before-after pairs should be found correctly`` b =
        b |> findBoolAfters |> Map.ofList

    /// Test cases for substituting afters in a func.
    static member AfterFuncs =
        [ TestCaseData({ Name = "foo"
                         Params = [ MExpr.Int (iAfter "serving")
                                    MExpr.Bool (bAfter "flag") ] })
            .Returns({ Name = "foo"
                       Params = [ MExpr.Int (AAdd [iBefore "serving"; AInt 1L])
                                  MExpr.Bool (BNot (bBefore "flag")) ] })
            .SetName("Substitute afters in a func with all-after params") ]

    /// Test substitution of afters in funcs.
    [<TestCaseSource("AfterFuncs")>]
    member x.``Afters in func params should be substituted correctly`` f =
        let sub = afterSubs OptimiserTests.AfterArithSubs
                            OptimiserTests.AfterBoolSubs
        subExprInVFunc sub f

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
    member x.``Boolean expressions should be simplified properly`` b =
        simp b
