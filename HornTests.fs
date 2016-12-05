/// <summary>
///     Tests for <c>Starling.Backends.Horn</c>.
/// </summary>
module Starling.Tests.Backends.Horn

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Utils.Testing
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Backends.Horn

/// Tests for Starling.Horn and Starling.HSF.
module Tests =
    /// The globals environment used in the tests.
    let SharedVars : VarMap =
        returnOrFail <| VarMap.ofTypedVarSeq
            [ normalIntVar "serving"
              normalIntVar "ticket" ]

    [<Test>]
    let ``Refuse modulo expressions``() =
        assertEqual
            (Some [ UnsupportedExpr (normalIntExpr (IMod (IInt 5L, IVar "foo"))) ])
            (checkArith id (IMod (IInt 5L, IVar "foo")) |> failOption)

    [<Test>]
    let ``Model the ticket lock view definitions as Horn clauses``() =
        let x : (DFunc * BoolExpr<string> option) list =
            [ ( { Name = "emp"
                  Params = [ normalIntVar "serving"
                             normalIntVar "ticket" ] },
                Some <| BGe(normalInt (IVar "ticket"), normalInt (IVar "serving")))
              ( { Name = "v_holdTick"
                  Params = [ normalIntVar "serving"
                             normalIntVar "ticket"
                             normalIntVar "t" ] },
                Some <| BGt(normalInt (IVar "ticket"), normalInt (IVar "t")))
              ( { Name = "v_holdLock"
                  Params = [ normalIntVar "serving"
                             normalIntVar "ticket" ] },
                Some <| BGt(normalInt (IVar "ticket"), normalInt (IVar "serving")))
              ( { Name = "v_holdLock_holdTick"
                  Params = [ normalIntVar "serving"
                             normalIntVar "ticket"
                             normalIntVar "t" ] },
                Some <| BNot(iEq (IVar "serving") (IVar "t")))
              ( { Name = "v_holdTick_holdTick"
                  Params = [ normalIntVar "serving"
                             normalIntVar "ticket"
                             normalIntVar "ta"
                             normalIntVar "tb" ] },
                Some <| BNot(iEq (IVar "ta") (IVar "tb")))
              ( { Name = "v_holdLock_holdLock"
                  Params = [ normalIntVar "serving"
                             normalIntVar "ticket" ] },
                Some <| BFalse ) ]
        Assert.That
            (x
             |> List.map hsfModelViewDef
             |> collect
             |> lift (List.concat >> Set.ofList)
             |> okOption,
             Is.EqualTo
                (Set.ofList
                    [ Clause(Ge (IVar "Vticket", IVar "Vserving"),
                             [ Pred { Name = "emp"
                                      Params = [ IVar "Vserving"; IVar "Vticket" ] } ] )
                      Clause(Gt (IVar "Vticket", IVar "Vt"),
                             [ Pred { Name = "v_holdTick"
                                      Params = [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] } ] )
                      Clause(Gt (IVar "Vticket", IVar "Vserving"),
                             [ Pred { Name = "v_holdLock"
                                      Params = [ IVar "Vserving"; IVar "Vticket" ] } ] )
                      Clause(Neq (IVar "Vserving", IVar "Vt"),
                             [ Pred { Name = "v_holdLock_holdTick"
                                      Params = [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] } ] )
                      Clause(Neq (IVar "Vta", IVar "Vtb"),
                             [ Pred { Name = "v_holdTick_holdTick"
                                      Params = [ IVar "Vserving"; IVar "Vticket"; IVar "Vta"; IVar "Vtb" ] } ] )
                      Clause(False,
                             [ Pred { Name = "v_holdLock_holdLock"
                                      Params = [ IVar "Vserving"; IVar "Vticket"] } ] )
                      Clause(Pred { Name = "emp"
                                    Params = [ IVar "Vserving"; IVar "Vticket" ] },
                             [ Ge (IVar "Vticket", IVar "Vserving") ] )
                      Clause(Pred { Name = "v_holdTick"
                                    Params = [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] },
                             [ Gt (IVar "Vticket", IVar "Vt") ] )
                      Clause(Pred { Name = "v_holdLock"
                                    Params = [ IVar "Vserving"; IVar "Vticket" ] },
                             [ Gt (IVar "Vticket", IVar "Vserving") ] )
                      Clause(Pred { Name = "v_holdLock_holdTick"
                                    Params = [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] },
                             [ Neq (IVar "Vserving", IVar "Vt") ] )
                      Clause(Pred { Name = "v_holdTick_holdTick"
                                    Params = [ IVar "Vserving"; IVar "Vticket"; IVar "Vta"; IVar "Vtb" ] },
                             [ Neq (IVar "Vta", IVar "Vtb") ] )
                      Clause(Pred { Name = "v_holdLock_holdLock"
                                    Params = [ IVar "Vserving"; IVar "Vticket"] },
                             [ False ] )

                      QueryNaming {Name = "emp"; Params = ["serving"; "ticket"]}
                      QueryNaming {Name = "v_holdTick"; Params = ["serving"; "ticket"; "t"]}
                      QueryNaming {Name = "v_holdLock"; Params = ["serving"; "ticket"]}
                      QueryNaming {Name = "v_holdLock_holdTick"; Params = ["serving"; "ticket"; "t"]}
                      QueryNaming {Name = "v_holdTick_holdTick"; Params = ["serving"; "ticket"; "ta"; "tb"]}
                      QueryNaming {Name = "v_holdLock_holdLock"; Params = ["serving"; "ticket"]}
                    ]
                |> Some : Set<Horn> option)
            )

    [<Test>]
    let ``the HSF variable initialiser works correctly using various variable maps``() =
        Assert.That(
            SharedVars |> hsfModelVariables |> okOption,
            Is.EqualTo(
                Clause (Pred { Name = "emp"
                               Params = [ IVar "Vserving"; IVar "Vticket" ] },
                        [ Eq (IVar "Vserving", IInt 0L)
                          Eq (IVar "Vticket", IInt 0L) ] )
            |> Some
        ))
