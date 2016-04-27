/// <summary>
///     Tests for <c>Starling.Backends.Horn</c>.
/// </summary>
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
              Some <| BGe(AVar "ticket", AVar "serving"))
            ( { Name = "v_holdTick"
                Params = [ Param.Int "serving"
                           Param.Int "ticket"
                           Param.Int "t" ] },
              Some <| BGt(AVar "ticket", AVar "t"))
            ( { Name = "v_holdLock"
                Params = [ Param.Int "serving"
                           Param.Int "ticket" ] },
              Some <| BGt(AVar "ticket", AVar "serving"))
            ( { Name = "v_holdLock_holdTick"
                Params = [ Param.Int "serving"
                           Param.Int "ticket"
                           Param.Int "t" ] },
              Some <| BNot(iEq (AVar "serving") (AVar "t")))
            ( { Name = "v_holdTick_holdTick"
                Params = [ Param.Int "serving"
                           Param.Int "ticket"
                           Param.Int "ta"
                           Param.Int "tb" ] },
              Some <| BNot(iEq (AVar "ta") (AVar "tb")))
            ( { Name = "v_holdLock_holdLock"
                Params = [ Param.Int "serving"
                           Param.Int "ticket" ] },
              Some <| BFalse ) ] )
          .Returns(
              Set.ofList
                  [ Clause(Ge (AVar "ticket", AVar "serving"),
                           [ Pred { Name = "emp"
                                    Params = [ AVar "serving"; AVar "ticket" ] } ] )
                    Clause(Gt (AVar "ticket", AVar "t"),
                           [ Pred { Name = "v_holdTick"
                                    Params = [ AVar "serving"; AVar "ticket"; AVar "t" ] } ] )
                    Clause(Gt (AVar "ticket", AVar "serving"),
                           [ Pred { Name = "v_holdLock"
                                    Params = [ AVar "serving"; AVar "ticket" ] } ] )
                    Clause(Neq (AVar "serving", AVar "t"),
                           [ Pred { Name = "v_holdLock_holdTick"
                                    Params = [ AVar "serving"; AVar "ticket"; AVar "t" ] } ] )
                    Clause(Neq (AVar "ta", AVar "tb"),
                           [ Pred { Name = "v_holdTick_holdTick"
                                    Params = [ AVar "serving"; AVar "ticket"; AVar "ta"; AVar "tb" ] } ] )
                    Clause(False,
                           [ Pred { Name = "v_holdLock_holdLock"
                                    Params = [ AVar "serving"; AVar "ticket"] } ] )
                    Clause(Pred { Name = "emp"
                                  Params = [ AVar "serving"; AVar "ticket" ] },
                           [ Ge (AVar "ticket", AVar "serving") ] )
                    Clause(Pred { Name = "v_holdTick"
                                  Params = [ AVar "serving"; AVar "ticket"; AVar "t" ] },
                           [ Gt (AVar "ticket", AVar "t") ] )
                    Clause(Pred { Name = "v_holdLock"
                                  Params = [ AVar "serving"; AVar "ticket" ] },
                           [ Gt (AVar "ticket", AVar "serving") ] )
                    Clause(Pred { Name = "v_holdLock_holdTick"
                                  Params = [ AVar "serving"; AVar "ticket"; AVar "t" ] },
                           [ Neq (AVar "serving", AVar "t") ] )

                    Clause(Pred { Name = "v_holdTick_holdTick"
                                  Params = [ AVar "serving"; AVar "ticket"; AVar "ta"; AVar "tb" ] },
                           [ Neq (AVar "ta", AVar "tb") ] )
                    Clause(Pred { Name = "v_holdLock_holdLock"
                                  Params = [ AVar "serving"; AVar "ticket"] },
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
                                 Params = [ AVar "serving"; AVar "ticket" ] },
                          [ Eq (AVar "serving", AInt 0L)
                            Eq (AVar "ticket", AInt 0L) ] )
              |> Some
          ).SetName("Model the ticket lock's variable initialisations as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("VariableModels")>]
    member x.``the HSF variable initialiser works correctly using various variable maps`` (gs: VarMap) =
        gs |> hsfModelVariables |> okOption
