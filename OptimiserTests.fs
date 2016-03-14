module Starling.Tests.Optimiser

open NUnit.Framework
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Sub
open Starling.Optimiser.Graph
open Starling.Optimiser.Term


/// Tests for the term optimiser.
type OptimiserTests() =
    (*
     * Graph optimisation
     *)

    /// <summary>
    ///     Test cases for checking whether a command is a no-op.
    /// </summary>
    static member Nops =
        [ TestCaseData(vfunc "Id" [])
            .Returns(true)
            .SetName("Classify Id() as a no-op")
          TestCaseData(vfunc "Assume" [ BExpr (bBefore "x") ])
            .Returns(true)
            .SetName("Classify Assume(x!before) as a no-op")
          TestCaseData(vfunc "Assume" [ BExpr (bAfter "x") ])
            .Returns(false)
            .SetName("Reject Assume(x!after) as a no-op")
          TestCaseData(vfunc "Foo" [ AExpr (aBefore "bar")
                                     AExpr (aAfter "bar") ] )
            .Returns(false)
            .SetName("Reject Foo(bar!before, bar!after as a no-op") ]

    /// <summary>
    ///     Tests <c>isNop</c>.
    /// </summary>
    [<TestCaseSource("Nops")>]
    member x.``Tests whether commands are correctly identified as no-ops`` c =
        isNop c


    (*
     * Term optimisation
     *)

    /// A test environment of arithmetic after substitutions.
    static member AfterArithSubs =
        [ ("serving", AAdd [aBefore "serving"; AInt 1L])
          ("ticket", aBefore "ticket") ]
        |> Map.ofList

    static member AfterBoolSubs =
        [ ("flag", BNot (bBefore "flag"))
          ("turn", bBefore "turn") ]
        |> Map.ofList

    /// Test cases for rewriting Boolean expressions containing afters.
    static member AfterBools =
        [ TestCaseData(aEq (aAfter "serving") (aAfter "ticket"))
            .Returns(aEq (AAdd [aBefore "serving"; AInt 1L])
                         (aBefore "ticket"))
            .SetName("Remove arithmetic afters in a simple equality")
          TestCaseData(aEq (aAfter "serving") (AAdd [aBefore "serving"
                                                     AInt 1L]))
            .Returns(aEq (AAdd [aBefore "serving"; AInt 1L])
                         (AAdd [aBefore "serving"; AInt 1L]))
            .SetName("Remove arithmetic afters in after-before relation")
          TestCaseData(BGt (aAfter "serving", aAfter "t"))
            .Returns(BGt (AAdd [aBefore "serving"; AInt 1L],
                          aAfter "t"))
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
          TestCaseData(BAnd [BGt (aAfter "serving", aAfter "t")
                             BOr [bAfter "flag"; bAfter "pole"]])
            .Returns(BAnd [ BGt ((AAdd [aBefore "serving"
                                        AInt 1L]), aAfter "t")
                            BOr [BNot (bBefore "flag"); bAfter "pole" ]])
            .SetName("Remove afters of both types simultaneously")
          TestCaseData(BNot (BImplies (bAfter "flag", BGt (aAfter "serving",
                                                           aAfter "t"))))
            .Returns(BNot (BImplies (BNot (bBefore "flag"),
                                     BGt (AAdd [aBefore "serving"; AInt 1L],
                                          aAfter "t"))))
            .SetName("Remove arithmetic afters from a complex expression")]

    /// Test after-elimination of Booleans.
    [<TestCaseSource("AfterBools")>]
    member x.``After-elimination of Booleans should operate correctly`` b =
        (afterSubs OptimiserTests.AfterArithSubs OptimiserTests.AfterBoolSubs)
            .BSub b

    /// Test cases for discovering Boolean after-before pairs.
    static member BoolAfterDiscoveries =
        let me : Map<string, BoolExpr> = Map.empty
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
                         Params = [ AExpr (aAfter "serving")
                                    BExpr (bAfter "flag") ] })
            .Returns({ Name = "foo"
                       Params = [ AExpr (AAdd [aBefore "serving"; AInt 1L])
                                  BExpr (BNot (bBefore "flag")) ] })
            .SetName("Substitute afters in a func with all-after params") ]

    /// Test substitution of afters in funcs.
    [<TestCaseSource("AfterFuncs")>]
    member x.``Afters in func params should be substituted correctly`` f =
        let sub = afterSubs OptimiserTests.AfterArithSubs
                            OptimiserTests.AfterBoolSubs
        subExprInVFunc sub f

    /// Test cases for simplification.
    static member ObviousBools =
        [ TestCaseData(BNot BFalse)
            .Returns(BTrue)
            .SetName("Simplify !false as a tautology")
          TestCaseData(BAnd [BTrue; BTrue; BNot BFalse; bEq BFalse BFalse])
            .Returns(BTrue)
            .SetName("Simplify true&&true&&!false&&false==false to true")
          TestCaseData(BImplies (BFalse, bEq BTrue BFalse))
            .Returns(BTrue)
            .SetName("Simplify false=>true==false to true")
          TestCaseData(BNot BTrue)
            .Returns(BFalse)
            .SetName("Simplify !true as a contradiction")
          TestCaseData(BAnd [BTrue; BFalse; BNot BFalse; bEq BFalse BFalse])
            .Returns(BFalse)
            .SetName("Simplify true&&false&&!false&&false==false to false")
          TestCaseData(BImplies (BTrue, bEq BTrue BFalse))
            .Returns(BFalse)
            .SetName("Simplify true=>true==false to false")
          TestCaseData(BImplies ((bAfter "s"), BFalse))
            .Returns(BNot (bAfter "s"))
            .SetName("Simplify =>False into a Negation")
          TestCaseData(BImplies ((bAfter "s"), BTrue))
            .Returns(BTrue)
            .SetName("Simplify =>True into a True")
          TestCaseData(BImplies (BGt ((aAfter "s"), (aAfter "t")), BFalse))
            .Returns(BLe ((aAfter "s"), (aAfter "t" )))
            .SetName("Simplify =>False wrapped around a > into <=")
          TestCaseData(BImplies (BTrue, (bAfter "s")))
            .Returns((bAfter "s"))
            .SetName("Simplify True=>s into s")
          TestCaseData(BImplies (BFalse, (bAfter "s")))
            .Returns(BTrue)
            .SetName("Simplify False=>s into True")
            ]

     /// Test Boolean simplification
    [<TestCaseSource("ObviousBools")>]
    member x.``Boolean expressions should be simplified properly`` b =
        simp b
