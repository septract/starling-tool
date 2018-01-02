/// <summary>
///     Tests for <c>Starling.Backends.Horn</c>.
/// </summary>
module Starling.Tests.Backends.Horn

open Chessie.ErrorHandling
open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.Collections
open Starling.Utils
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Backends.Horn

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
        [ ( func "emp"
              [ normalIntVar "serving"
                normalIntVar "ticket" ],
            Some <| BGe(normalInt (IVar "ticket"), normalInt (IVar "serving")))
          ( func "v_holdTick"
              [ normalIntVar "serving"
                normalIntVar "ticket"
                normalIntVar "t" ],
            Some <| BGt(normalInt (IVar "ticket"), normalInt (IVar "t")))
          ( func "v_holdLock"
              [ normalIntVar "serving"
                normalIntVar "ticket" ],
            Some <| BGt(normalInt (IVar "ticket"), normalInt (IVar "serving")))
          ( func "v_holdLock_holdTick"
              [ normalIntVar "serving"
                normalIntVar "ticket"
                normalIntVar "t" ],
            Some <| BNot(iEq (IVar "serving") (IVar "t")))
          ( func "v_holdTick_holdTick"
              [ normalIntVar "serving"
                normalIntVar "ticket"
                normalIntVar "ta"
                normalIntVar "tb" ],
            Some <| BNot(iEq (IVar "ta") (IVar "tb")))
          ( func "v_holdLock_holdLock"
              [ normalIntVar "serving"
                normalIntVar "ticket" ],
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
                         [ Pred (func "emp" [ IVar "Vserving"; IVar "Vticket" ] ) ] )
                  Clause(Gt (IVar "Vticket", IVar "Vt"),
                         [ Pred (func "v_holdTick" [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] ) ] )
                  Clause(Gt (IVar "Vticket", IVar "Vserving"),
                         [ Pred (func "v_holdLock" [ IVar "Vserving"; IVar "Vticket" ] ) ] )
                  Clause(Neq (IVar "Vserving", IVar "Vt"),
                         [ Pred (func "v_holdLock_holdTick" [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] ) ] )
                  Clause(Neq (IVar "Vta", IVar "Vtb"),
                         [ Pred (func "v_holdTick_holdTick" [ IVar "Vserving"; IVar "Vticket"; IVar "Vta"; IVar "Vtb" ] ) ] )
                  Clause(False,
                         [ Pred (func "v_holdLock_holdLock" [ IVar "Vserving"; IVar "Vticket"] ) ] )
                  Clause(Pred (func "emp" [ IVar "Vserving"; IVar "Vticket" ] ),
                         [ Ge (IVar "Vticket", IVar "Vserving") ] )
                  Clause(Pred (func "v_holdTick" [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] ),
                         [ Gt (IVar "Vticket", IVar "Vt") ] )
                  Clause(Pred (func "v_holdLock" [ IVar "Vserving"; IVar "Vticket" ] ),
                         [ Gt (IVar "Vticket", IVar "Vserving") ] )
                  Clause(Pred (func "v_holdLock_holdTick" [ IVar "Vserving"; IVar "Vticket"; IVar "Vt" ] ),
                         [ Neq (IVar "Vserving", IVar "Vt") ] )
                  Clause(Pred (func "v_holdTick_holdTick" [ IVar "Vserving"; IVar "Vticket"; IVar "Vta"; IVar "Vtb" ] ),
                         [ Neq (IVar "Vta", IVar "Vtb") ] )
                  Clause(Pred (func "v_holdLock_holdLock" [ IVar "Vserving"; IVar "Vticket"] ),
                         [ False ] )

                  QueryNaming (func "emp" ["serving"; "ticket"])
                  QueryNaming (func "v_holdTick" ["serving"; "ticket"; "t"])
                  QueryNaming (func "v_holdLock" ["serving"; "ticket"])
                  QueryNaming (func "v_holdLock_holdTick" ["serving"; "ticket"; "t"])
                  QueryNaming (func "v_holdTick_holdTick" ["serving"; "ticket"; "ta"; "tb"])
                  QueryNaming (func "v_holdLock_holdLock" ["serving"; "ticket"])
                ]
            |> Some : Set<Horn> option)
        )

[<Test>]
let ``the HSF variable initialiser works correctly using various variable maps``() =
    Assert.That(
        SharedVars |> hsfModelVariables |> okOption,
        Is.EqualTo(
            Clause (Pred (func "emp" [ IVar "Vserving"; IVar "Vticket" ]),
                    [ Eq (IVar "Vserving", IInt 0L)
                      Eq (IVar "Vticket", IInt 0L) ] )
        |> Some
    ))
