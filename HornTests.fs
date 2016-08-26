/// <summary>
///     Tests for <c>Starling.Backends.Horn</c>.
/// </summary>
module Starling.Tests.Backends.Horn

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Model
open Starling.Backends.Horn
open Starling.Tests.Studies

/// Tests for Starling.Horn and Starling.HSF.
module Tests =
    /// The globals environment used in the tests.
    let Globals : VarMap =
        returnOrFail <| makeVarMap
            [ TypedVar.Int "serving"
              TypedVar.Int "ticket" ]

    [<Test>]
    let ``Model the ticket lock view definitions as Horn clauses``() =
        let x : (DFunc * BoolExpr<string> option) list =
            [ ( { Name = "emp"
                  Params = [ Int "serving"
                             Int "ticket" ] },
                Some <| BGe(AVar "ticket", AVar "serving"))
              ( { Name = "v_holdTick"
                  Params = [ Int "serving"
                             Int "ticket"
                             Int "t" ] },
                Some <| BGt(AVar "ticket", AVar "t"))
              ( { Name = "v_holdLock"
                  Params = [ Int "serving"
                             Int "ticket" ] },
                Some <| BGt(AVar "ticket", AVar "serving"))
              ( { Name = "v_holdLock_holdTick"
                  Params = [ Int "serving"
                             Int "ticket"
                             Int "t" ] },
                Some <| BNot(iEq (AVar "serving") (AVar "t")))
              ( { Name = "v_holdTick_holdTick"
                  Params = [ Int "serving"
                             Int "ticket"
                             Int "ta"
                             Int "tb" ] },
                Some <| BNot(iEq (AVar "ta") (AVar "tb")))
              ( { Name = "v_holdLock_holdLock"
                  Params = [ Int "serving"
                             Int "ticket" ] },
                Some <| BFalse ) ]
        Assert.That
            (x
             |> List.map hsfModelViewDef
             |> collect
             |> lift (List.concat >> Set.ofList)
             |> okOption,
             Is.EqualTo
                (Set.ofList
                    [ Clause(Ge (AVar "Vticket", AVar "Vserving"),
                             [ Pred { Name = "emp"
                                      Params = [ AVar "Vserving"; AVar "Vticket" ] } ] )
                      Clause(Gt (AVar "Vticket", AVar "Vt"),
                             [ Pred { Name = "v_holdTick"
                                      Params = [ AVar "Vserving"; AVar "Vticket"; AVar "Vt" ] } ] )
                      Clause(Gt (AVar "Vticket", AVar "Vserving"),
                             [ Pred { Name = "v_holdLock"
                                      Params = [ AVar "Vserving"; AVar "Vticket" ] } ] )
                      Clause(Neq (AVar "Vserving", AVar "Vt"),
                             [ Pred { Name = "v_holdLock_holdTick"
                                      Params = [ AVar "Vserving"; AVar "Vticket"; AVar "Vt" ] } ] )
                      Clause(Neq (AVar "Vta", AVar "Vtb"),
                             [ Pred { Name = "v_holdTick_holdTick"
                                      Params = [ AVar "Vserving"; AVar "Vticket"; AVar "Vta"; AVar "Vtb" ] } ] )
                      Clause(False,
                             [ Pred { Name = "v_holdLock_holdLock"
                                      Params = [ AVar "Vserving"; AVar "Vticket"] } ] )
                      Clause(Pred { Name = "emp"
                                    Params = [ AVar "Vserving"; AVar "Vticket" ] },
                             [ Ge (AVar "Vticket", AVar "Vserving") ] )
                      Clause(Pred { Name = "v_holdTick"
                                    Params = [ AVar "Vserving"; AVar "Vticket"; AVar "Vt" ] },
                             [ Gt (AVar "Vticket", AVar "Vt") ] )
                      Clause(Pred { Name = "v_holdLock"
                                    Params = [ AVar "Vserving"; AVar "Vticket" ] },
                             [ Gt (AVar "Vticket", AVar "Vserving") ] )
                      Clause(Pred { Name = "v_holdLock_holdTick"
                                    Params = [ AVar "Vserving"; AVar "Vticket"; AVar "Vt" ] },
                             [ Neq (AVar "Vserving", AVar "Vt") ] )
                      Clause(Pred { Name = "v_holdTick_holdTick"
                                    Params = [ AVar "Vserving"; AVar "Vticket"; AVar "Vta"; AVar "Vtb" ] },
                             [ Neq (AVar "Vta", AVar "Vtb") ] )
                      Clause(Pred { Name = "v_holdLock_holdLock"
                                    Params = [ AVar "Vserving"; AVar "Vticket"] },
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
            Globals |> hsfModelVariables |> okOption,
            Is.EqualTo(
                Clause (Pred { Name = "emp"
                               Params = [ AVar "Vserving"; AVar "Vticket" ] },
                        [ Eq (AVar "Vserving", AInt 0L)
                          Eq (AVar "Vticket", AInt 0L) ] )
            |> Some
        ))