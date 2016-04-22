/// Tests for Starling.Backends.Horn and
module Starling.Tests.Backends.Horn

open Chessie.ErrorHandling
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
    static member Globals : VarMap =
        returnOrFail <| makeVarMap
            [ VarDecl.Int "serving"
              VarDecl.Int "ticket" ]


    /// Test cases for the viewdef Horn clause modeller.
    /// These are in the form of models whose viewdefs are to be modelled.
    static member ViewDefModels =
      [ TestCaseData(
          [ ( { Name = "emp"
                Params = [ Param.Int "serving"
                           Param.Int "ticket" ] },
              Some <| BGe(iUnmarked "ticket", iUnmarked "serving"))
            ( { Name = "v_holdTick"
                Params = [ Param.Int "serving"
                           Param.Int "ticket"
                           Param.Int "t" ] },
              Some <| BGt(iUnmarked "ticket", iUnmarked "t"))
            ( { Name = "v_holdLock"
                Params = [ Param.Int "serving"
                           Param.Int "ticket" ] },
              Some <| BGt(iUnmarked "ticket", iUnmarked "serving"))
            ( { Name = "v_holdLock_holdTick"
                Params = [ Param.Int "serving"
                           Param.Int "ticket"
                           Param.Int "t" ] },
              Some <| BNot(iEq (iUnmarked "serving") (iUnmarked "t")))
            ( { Name = "v_holdTick_holdTick"
                Params = [ Param.Int "serving"
                           Param.Int "ticket"
                           Param.Int "ta"
                           Param.Int "tb" ] },
              Some <| BNot(iEq (iUnmarked "ta") (iUnmarked "tb")))
            ( { Name = "v_holdLock_holdLock"
                Params = [ Param.Int "serving"
                           Param.Int "ticket" ] },
              Some <| BFalse ) ] )
          .Returns(
              Set.ofList
                  [ Clause(Ge (iUnmarked "ticket", iUnmarked "serving"),
                           [ Pred { Name = "emp"
                                    Params = [ iUnmarked "serving"; iUnmarked "ticket" ] } ] )
                    Clause(Gt (iUnmarked "ticket", iUnmarked "t"),
                           [ Pred { Name = "v_holdTick"
                                    Params = [ iUnmarked "serving"; iUnmarked "ticket"; iUnmarked "t" ] } ] )
                    Clause(Gt (iUnmarked "ticket", iUnmarked "serving"),
                           [ Pred { Name = "v_holdLock"
                                    Params = [ iUnmarked "serving"; iUnmarked "ticket" ] } ] )
                    Clause(Neq (iUnmarked "serving", iUnmarked "t"),
                           [ Pred { Name = "v_holdLock_holdTick"
                                    Params = [ iUnmarked "serving"; iUnmarked "ticket"; iUnmarked "t" ] } ] )
                    Clause(Neq (iUnmarked "ta", iUnmarked "tb"),
                           [ Pred { Name = "v_holdTick_holdTick"
                                    Params = [ iUnmarked "serving"; iUnmarked "ticket"; iUnmarked "ta"; iUnmarked "tb" ] } ] )
                    Clause(False,
                           [ Pred { Name = "v_holdLock_holdLock"
                                    Params = [ iUnmarked "serving"; iUnmarked "ticket"] } ] )
                    Clause(Pred { Name = "emp"
                                  Params = [ iUnmarked "serving"; iUnmarked "ticket" ] },
                           [ Ge (iUnmarked "ticket", iUnmarked "serving") ] )
                    Clause(Pred { Name = "v_holdTick"
                                  Params = [ iUnmarked "serving"; iUnmarked "ticket"; iUnmarked "t" ] },
                           [ Gt (iUnmarked "ticket", iUnmarked "t") ] )
                    Clause(Pred { Name = "v_holdLock"
                                  Params = [ iUnmarked "serving"; iUnmarked "ticket" ] },
                           [ Gt (iUnmarked "ticket", iUnmarked "serving") ] )
                    Clause(Pred { Name = "v_holdLock_holdTick"
                                  Params = [ iUnmarked "serving"; iUnmarked "ticket"; iUnmarked "t" ] },
                           [ Neq (iUnmarked "serving", iUnmarked "t") ] )

                    Clause(Pred { Name = "v_holdTick_holdTick"
                                  Params = [ iUnmarked "serving"; iUnmarked "ticket"; iUnmarked "ta"; iUnmarked "tb" ] },
                           [ Neq (iUnmarked "ta", iUnmarked "tb") ] )
                    Clause(Pred { Name = "v_holdLock_holdLock"
                                  Params = [ iUnmarked "serving"; iUnmarked "ticket"] },
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
                                 Params = [ iUnmarked "serving"; iUnmarked "ticket" ] },
                          [ Eq (iUnmarked "serving", AInt 0L)
                            Eq (iUnmarked "ticket", AInt 0L) ] )
              |> Some
          ).SetName("Model the ticket lock's variable initialisations as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("VariableModels")>]
    member x.``the HSF variable initialiser works correctly using various variable maps`` (gs: VarMap) =
        gs |> hsfModelVariables |> okOption
