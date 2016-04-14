/// Tests for Starling.Backends.Horn and
module Starling.Tests.Backends.Horn

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Backends.Horn
open Starling.Tests.Studies

/// Tests for Starling.Horn and Starling.HSF.
type HornTests() =
    /// The globals environment used in the tests.
    static member Globals =
        Map.ofList [ ("serving", Type.Int) ; ("ticket", Type.Int) ]

    /// Test cases for the viewdef Horn clause modeller.
    /// These are in the form of models whose viewdefs are to be modelled.
    static member ViewDefModels =
      [ TestCaseData(
          [ Definite
                ( { Name = "emp"
                    Params = [ (Type.Int, "serving")
                               (Type.Int, "ticket") ] },
                  BGe(aUnmarked "ticket", aUnmarked "serving"))
            Definite
                ( { Name = "v_holdTick"
                    Params = [ (Type.Int, "serving")
                               (Type.Int, "ticket")
                               (Type.Int, "t") ] },
                  BGt(aUnmarked "ticket", aUnmarked "t"))
            Definite
                ( { Name = "v_holdLock"
                    Params = [ (Type.Int, "serving")
                               (Type.Int, "ticket") ] },
                  BGt(aUnmarked "ticket", aUnmarked "serving"))
            Definite
                ( { Name = "v_holdLock_holdTick"
                    Params = [ (Type.Int, "serving")
                               (Type.Int, "ticket")
                               (Type.Int, "t") ] },
                  BNot(aEq (aUnmarked "serving") (aUnmarked "t")))
            Definite
                ( { Name = "v_holdTick_holdTick"
                    Params = [ (Type.Int, "serving")
                               (Type.Int, "ticket")
                               (Type.Int, "ta")
                               (Type.Int, "tb") ] },
                  BNot(aEq (aUnmarked "ta") (aUnmarked "tb")))
            Definite
                ( { Name = "v_holdLock_holdLock"
                    Params = [ (Type.Int, "serving")
                               (Type.Int, "ticket") ] },
                  BFalse ) ] )
          .Returns(
              Set.ofList
                  [ Clause(Ge (aUnmarked "ticket", aUnmarked "serving"),
                           [ Pred { Name = "emp"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket" ] } ] )
                    Clause(Gt (aUnmarked "ticket", aUnmarked "t"),
                           [ Pred { Name = "v_holdTick"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] } ] )
                    Clause(Gt (aUnmarked "ticket", aUnmarked "serving"),
                           [ Pred { Name = "v_holdLock"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket" ] } ] )
                    Clause(Neq (aUnmarked "serving", aUnmarked "t"),
                           [ Pred { Name = "v_holdLock_holdTick"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] } ] )
                    Clause(Neq (aUnmarked "ta", aUnmarked "tb"),
                           [ Pred { Name = "v_holdTick_holdTick"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "ta"; aUnmarked "tb" ] } ] )
                    Clause(False,
                           [ Pred { Name = "v_holdLock_holdLock"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket"] } ] )
                    Clause(Pred { Name = "emp"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket" ] },
                           [ Ge (aUnmarked "ticket", aUnmarked "serving") ] )
                    Clause(Pred { Name = "v_holdTick"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] },
                           [ Gt (aUnmarked "ticket", aUnmarked "t") ] )
                    Clause(Pred { Name = "v_holdLock"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket" ] },
                           [ Gt (aUnmarked "ticket", aUnmarked "serving") ] )
                    Clause(Pred { Name = "v_holdLock_holdTick"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] },
                           [ Neq (aUnmarked "serving", aUnmarked "t") ] )

                    Clause(Pred { Name = "v_holdTick_holdTick"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "ta"; aUnmarked "tb" ] },
                           [ Neq (aUnmarked "ta", aUnmarked "tb") ] )
                    Clause(Pred { Name = "v_holdLock_holdLock"
                                  Params = [ aUnmarked "serving"; aUnmarked "ticket"] },
                           [ False ] )

                    QueryNaming {Name = "emp"; Params = ["serving"; "ticket"]}
                    QueryNaming {Name = "v_holdTick"; Params = ["serving"; "ticket"; "t"]}
                    QueryNaming {Name = "v_holdLock"; Params = ["serving"; "ticket"]}
                    QueryNaming {Name = "v_holdLock_holdTick"; Params = ["serving"; "ticket"; "t"]}
                    QueryNaming {Name = "v_holdTick_holdTick"; Params = ["serving"; "ticket"; "ta"; "tb"]}
                    QueryNaming {Name = "v_holdLock_holdLock"; Params = ["serving"; "ticket"]}
                  ]
              |> Some
          ).SetName("Model the ticket lock's viewdefs as Horn clauses") ]

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
                  Clause (Pred { Name = "emp"
                                 Params = [ aUnmarked "serving"; aUnmarked "ticket" ] },
                          [ Eq (aUnmarked "serving", AInt 0L)
                            Eq (aUnmarked "ticket", AInt 0L) ] )
              |> Some
          ).SetName("Model the ticket lock's variable initialisations as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("VariableModels")>]
    member x.``the HSF variable initialiser works correctly using various variable maps`` (gs: VarMap) =
        gs |> hsfModelVariables |> okOption
