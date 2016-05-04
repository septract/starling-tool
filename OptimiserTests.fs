/// <summary>
///     Tests for the optimiser.
/// </summary>
module Starling.Tests.Optimiser

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Model.Sub
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

    /// Test cases for rewriting Boolean expressions containing afters.
    static member AfterBools =
        [ TestCaseData(iEq (siAfter "serving") (siAfter "ticket"))
              .Returns(iEq
                           (AAdd [ siBefore "serving"; AInt 1L ] )
                           (siBefore "ticket"))
              .SetName("Remove arithmetic afters in a simple equality")
          TestCaseData(iEq
                           (siAfter "serving")
                           (AAdd [ siBefore "serving"; AInt 1L ] ))
              .Returns(iEq
                           (AAdd [ siBefore "serving"; AInt 1L ] )
                           (AAdd [ siBefore "serving"; AInt 1L ] ))
              .SetName("Remove arithmetic afters in after-before relation")
          TestCaseData(BGt (siAfter "serving", siAfter "t"))
              .Returns(BGt
                           (AAdd [ siBefore "serving"; AInt 1L ],
                            siAfter "t"))
              .SetName("Remove arithmetic afters only if in the environment")
          TestCaseData(bEq (sbAfter "flag") (sbAfter "turn"))
              .Returns(bEq
                           (BNot (sbBefore "flag"))
                           (sbBefore "turn"))
              .SetName("Remove Boolean afters in a simple equality")
          TestCaseData(bEq (sbAfter "flag") (BNot (sbBefore "flag")))
              .Returns(bEq
                           (BNot (sbBefore "flag"))
                           (BNot (sbBefore "flag")))
              .SetName("Remove Boolean afters in after-before relation")
          TestCaseData(BAnd [ sbAfter "flag"; sbAfter "pole" ] )
              .Returns(BAnd [ BNot (sbBefore "flag")
                              sbAfter "pole" ])
              .SetName("Remove Boolean afters only if in the environment")
          TestCaseData(BAnd
                           [ BGt (siAfter "serving", siAfter "t")
                             BOr [ sbAfter "flag"; sbAfter "pole" ]] )
              .Returns(BAnd
                           [ BGt
                                 ((AAdd [ siBefore "serving"; AInt 1L ] ),
                                  siAfter "t")
                             BOr [ BNot (sbBefore "flag"); sbAfter "pole" ]] )
              .SetName("Remove afters of both types simultaneously")
          TestCaseData(BNot
                           (BImplies
                                (sbAfter "flag",
                                 BGt
                                     (siAfter "serving",
                                      siAfter "t"))))
              .Returns(BNot
                           (BImplies
                                (BNot (sbBefore "flag"),
                                 BGt
                                     (AAdd [siBefore "serving"; AInt 1L],
                                      siAfter "t"))))
            .SetName("Remove arithmetic afters from a complex expression")]

    /// Test after-elimination of Booleans.
    [<TestCaseSource("AfterBools")>]
    member x.``After-elimination of Booleans should operate correctly`` b =
        Mapper.mapBool
            (afterSubs OptimiserTests.AfterArithSubs OptimiserTests.AfterBoolSubs)
            b

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

    /// Test cases for substituting afters in a func.
    static member AfterFuncs =
        [ TestCaseData({ Name = "foo"
                         Params = [ SMExpr.Int (siAfter "serving")
                                    SMExpr.Bool (sbAfter "flag") ] })
              .Returns({ Name = "foo"
                         Params = [ SMExpr.Int (AAdd [siBefore "serving"; AInt 1L])
                                    SMExpr.Bool (BNot (sbBefore "flag")) ] })
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
    member x.``Boolean expressions should be simplified properly`` (b : BoolExpr<MarkedVar>) =
        simp b
