/// Tests for Starling.Horn.

module Starling.Tests.Horn

open NUnit.Framework
open Starling.Utils
open Starling.Expr
open Starling.Horn
open Starling.Errors.Horn

/// Tests for Starling.Horn.
type HornTests() =
    /// Test cases for the Horn emitter.
    static member HornEmissions =
        [ TestCaseData({ Head = Gt(aBefore "ticket", aBefore "t")
                         Body = [ Pred { Name = "holdTick"
                                         Params = [ aAfter "t"
                                                    aBefore "serving"
                                                    aBefore "ticket" ] } ] })
            .Returns(Some <| "VticketB > VtB :- holdTick(VtA, VservingB, VticketB).")
          TestCaseData({ Head = False
                         Body = [ Pred { Name = "quux"
                                         Params = [ AAdd [AInt 5L
                                                          AInt 4L
                                                          AInt 3L
                                                          AInt 2L
                                                          AInt 1L] ] } ] })
            .Returns(Some <| "false :- quux(5 + 4 + 3 + 2 + 1).") ]
        |> List.map (fun d -> d.SetName(sprintf "Emit %A" d.ExpectedResult))

    /// Tests the Horn emitter.
    [<TestCaseSource("HornEmissions")>]
    member x.``the Horn clause emitter emits valid Horn clauses`` hc =
        emit hc |> okOption

    /// Failing test cases for the Horn emitter.
    static member BadHornEmissions =
        [ TestCaseData({ Head = Gt(aBefore "ticket", AAdd [])
                         Body = [ Pred { Name = "holdTick"
                                         Params = [ aAfter "t"
                                                    aBefore "serving"
                                                    aBefore "ticket" ] } ] })
            .Returns(Some <| [EmptyCompoundExpr "addition"])
            .SetName("Reject Horn clauses containing empty additions")
        ]

    /// Tests the Horn emitter on bad clauses.
    [<TestCaseSource("BadHornEmissions")>]
    member x.``the Horn clause emitter refuses to emit invalid Horn clauses`` hc =
        emit hc |> failOption

