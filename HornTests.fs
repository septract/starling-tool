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
        ]
        |> List.map (fun d -> d.SetName(sprintf "Emit %A" d.ExpectedResult))

    /// Tests the Horn emitter.
    [<TestCaseSource("HornEmissions")>]
    member x.``the Horn clause emitter emits valid Horn clauses`` hc =
        emit hc |> okOption

