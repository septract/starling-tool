/// Tests for Starling.Horn and Starling.HSF.
module Starling.Tests.Horn

open NUnit.Framework
open Starling.Collections
open Starling.Var
open Starling.Utils
open Starling.Expr
open Starling.Model
open Starling.Horn
open Starling.Tests.Studies

/// Tests for Starling.Horn and Starling.HSF.
type HornTests() =
    /// The globals environment used in the tests.
    static member Globals =
        Map.ofList [ ("serving", Type.Int) ; ("ticket", Type.Int) ]

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
                              Params = [ (Type.Int, "serving")
                                         (Type.Int, "ticket") ] }
                            { Name = "holdTick"
                              Params = [ (Type.Int, "serving")
                                         (Type.Int, "ticket")
                                         (Type.Int, "t") ] } ]).Returns(Some <| Pred { Name = "v_holdLock_holdTick"
                                                                                       Params =
                                                                                           [ aUnmarked "serving"
                                                                                             aUnmarked "ticket"
                                                                                             aUnmarked "t" ] })
            .SetName("List HSF params of ticketed lock view 'holdLock() * holdTick(t)' as serving, ticket, and t") ]

    /// Tests the viewdef LHS translator.
    [<TestCaseSource("ViewDefHeads")>]
    member x.``the HSF viewdef LHS translator works correctly using the ticketed lock model`` v =
        v
        |> predOfMultiset ticketLockModel.Globals ensureArith
        |> okOption

    /// Test cases for the viewdef Horn clause modeller.
    /// These are in the form of models whose viewdefs are to be modelled.
    static member ViewDefModels =
      [ TestCaseData(
          [ { CViews =
                  Multiset.ofList [ { Name = "emp"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket") ] } ]
              CExpr = Some <| BGe(aUnmarked "ticket", aUnmarked "serving") }
            { CViews = 
                  Multiset.ofList [ { Name = "holdTick"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket")
                                                 (Type.Int, "t") ] } ]
              CExpr = Some <| BGt(aUnmarked "ticket", aUnmarked "t") }
            { CViews = 
                  Multiset.ofList [ { Name = "holdLock"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket") ] } ]
              CExpr = Some <| BGt(aUnmarked "ticket", aUnmarked "serving") }
            { CViews = 
                  Multiset.ofList [ { Name = "holdLock"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket") ] }
                                    { Name = "holdTick"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket")
                                                 (Type.Int, "t") ] } ]
              CExpr = Some <| BNot(aEq (aUnmarked "serving") (aUnmarked "t")) }
            { CViews = 
                  Multiset.ofList [ { Name = "holdTick"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket")
                                                 (Type.Int, "ta") ] }
                                    { Name = "holdTick"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket")
                                                 (Type.Int, "tb") ] } ]
              CExpr = Some <| BNot(aEq (aUnmarked "ta") (aUnmarked "tb")) }
            { CViews = 
                  Multiset.ofList [ { Name = "holdLock"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket") ] }
                                    { Name = "holdLock"
                                      Params = [ (Type.Int, "serving")
                                                 (Type.Int, "ticket") ] } ]
              CExpr = Some <| BFalse } ] )
          .Returns(
              Set.ofList
                  [ { Head = Ge (aUnmarked "ticket", aUnmarked "serving")
                      Body = [ Pred { Name = "v_emp"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket" ] } ] }
                    { Head = Gt (aUnmarked "ticket", aUnmarked "t")
                      Body = [ Pred { Name = "v_holdTick"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] } ] }
                    { Head = Gt (aUnmarked "ticket", aUnmarked "serving")
                      Body = [ Pred { Name = "v_holdLock"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket" ] } ] }
                    { Head = Neq (aUnmarked "serving", aUnmarked "t")
                      Body = [ Pred { Name = "v_holdLock_holdTick"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] } ] }
                    { Head = Neq (aUnmarked "ta", aUnmarked "tb")
                      Body = [ Pred { Name = "v_holdTick_holdTick"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "ta"; aUnmarked "tb" ] } ] }
                    { Head = False
                      Body = [ Pred { Name = "v_holdLock_holdLock"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"] } ] }
                  ]
              |> Some
          ).SetName("Model the ticketed lock's viewdefs as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("ViewDefModels")>]
    member x.``the HSF model viewdef translator works correctly using various models`` dvs =
        let y = hsfModelViewDefs HornTests.Globals dvs
        y |> okOption

    /// Test cases for the variable Horn clause modeller.
    /// These are in the form of models whose viewdefs are to be modelled.
    static member VariableModels =
      [ TestCaseData(HornTests.Globals)
          .Returns(
                  { Head = Pred { Name = "v_emp"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket" ] }
                    Body = [ Eq (aUnmarked "serving", AInt 0L)
                             Eq (aUnmarked "ticket", AInt 0L) ] }
              |> Some
          ).SetName("Model the ticketed lock's variable initialisations as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("VariableModels")>]
    member x.``the HSF variable initialiser works correctly using various variable maps`` (gs: VarMap) =
        gs |> hsfModelVariables |> okOption
