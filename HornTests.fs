/// Tests for Starling.Horn and Starling.HSF.
module Starling.Tests.Horn

open NUnit.Framework
open Starling.Collections
open Starling.Var
open Starling.Utils
open Starling.Expr
open Starling.Model
open Starling.Horn
open Starling.HSF
open Starling.Errors.Horn
open Starling.Tests.Studies

/// Tests for Starling.Horn and Starling.HSF.
type HornTests() = 
    
    /// Test cases for the Horn emitter.
    static member HornEmissions = 
        [ TestCaseData({ Head = Gt(aBefore "ticket", aBefore "t")
                         Body = 
                             [ Pred { Name = "holdTick"
                                      Params = 
                                          [ aAfter "t"
                                            aBefore "serving"
                                            aBefore "ticket" ] } ] })
              .Returns(Some <| "VticketB > VtB :- holdTick(VtA, VservingB, VticketB).")
          
          TestCaseData({ Head = False
                         Body = 
                             [ Pred { Name = "quux"
                                      Params = 
                                          [ AAdd [ AInt 5L
                                                   AInt 4L
                                                   AInt 3L
                                                   AInt 2L
                                                   AInt 1L ] ] } ] })
              .Returns(Some <| "false :- quux(5 + 4 + 3 + 2 + 1).") ]
        |> List.map (fun d -> d.SetName(sprintf "Emit %A" d.ExpectedResult))
    
    /// Tests the Horn emitter.
    [<TestCaseSource("HornEmissions")>]
    member x.``the Horn clause emitter emits valid Horn clauses`` hc = emit hc |> okOption
    
    /// Failing test cases for the Horn emitter.
    static member BadHornEmissions = 
        [ TestCaseData({ Head = Gt(aBefore "ticket", AAdd [])
                         Body = 
                             [ Pred { Name = "holdTick"
                                      Params = 
                                          [ aAfter "t"
                                            aBefore "serving"
                                            aBefore "ticket" ] } ] }).Returns(Some <| [ EmptyCompoundExpr "addition" ])
            .SetName("Reject Horn clauses containing empty additions") ]
    
    /// Tests the Horn emitter on bad clauses.
    [<TestCaseSource("BadHornEmissions")>]
    member x.``the Horn clause emitter refuses to emit invalid Horn clauses`` hc = emit hc |> failOption
    
    /// Test cases for the multiset predicate renamer.
    static member ViewPredNamings = 
        let ms : View list -> Multiset<View> = Multiset.ofList
        [ TestCaseData(ms [ { Name = "foo"
                              Params = [] }
                            { Name = "bar_baz"
                              Params = [] } ]).Returns("v_bar__baz_foo") // Remember, multisets sort!
            .SetName("Encode HSF name of view 'foo() * bar_baz()' as 'v_bar__baz_foo'") ]
    
    /// Tests the view predicate name generator.
    [<TestCaseSource("ViewPredNamings")>]
    member x.``the HSF predicate name generator generates names correctly`` v = 
        let pn : Multiset<View> -> string = predNameOfMultiset
        pn v
    
    /// Test cases for the viewdef variable extractor.
    /// These all use the ticketed lock model.
    static member ViewDefHeads = 
        let ms : ViewDef list -> Multiset<ViewDef> = Multiset.ofList
        [ TestCaseData(ms [ { Name = "holdLock"
                              Params = [] }
                            { Name = "holdTick"
                              Params = [ (Type.Int, "t") ] } ]).Returns(Some <| Pred { Name = "v_holdLock_holdTick"
                                                                                       Params = 
                                                                                           [ aUnmarked "serving"
                                                                                             aUnmarked "ticket"
                                                                                             aUnmarked "t" ] })
            .SetName("List HSF params of ticketed lock view 'holdLock() * holdTick(t)' as serving, ticket, and t") ]
    
    /// Tests the viewdef LHS translator.
    [<TestCaseSource("ViewDefHeads")>]
    member x.``the HSF viewdef LHS translator works correctly using the ticketed lock model`` v = 
        v
        |> bodyOfConstraint (ticketLockModel.Globals
                             |> Map.toSeq
                             |> Seq.map fst
                             |> Set.ofSeq)
        |> okOption
