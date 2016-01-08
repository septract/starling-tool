module Starling.Tests.Modeller

open NUnit.Framework
open Chessie.ErrorHandling // ok
open Starling
open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Lang.AST
open Starling.Lang.Modeller
open Starling.Tests.Studies
open Starling.Pretty.Lang.AST

/// Tests for the modeller.
type ModellerTests() =
    /// Sample environment used in expression modelling tests.
    static member Env =
        Map.ofList
            [ ("foo", Type.Int)
              ("bar", Type.Int)
              ("baz", Type.Bool)
              ("emp", Type.Bool) ]

    /// Arithmetic expression modelling tests.
    static member ArithmeticExprs =
        seq {
            yield (
                new TestCaseData(
                    Bop(Add, Bop(Mul, Int 1L, Int 2L), Int 3L)
                )
            ).Returns(
                ok <| AAdd [ AMul [ AInt 1L ; AInt 2L ] ; AInt 3L ]
            ).SetName("model (1 * 2) + 3")
        }

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("ArithmeticExprs")>]
    member x.``test the arithmetic expression modeller`` ast =
        modelArithExpr ModellerTests.Env ast

    /// Boolean expression modelling tests.
    /// These all use the ticketed lock model.
    static member BooleanExprs =
        seq {
            yield (
                new TestCaseData(
                    Bop(And, Bop(Or, True, True), False)
                )
            ).Returns(
                ok (BFalse)
            ).SetName("model and simplify (true || true) && false")
        }


    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("BooleanExprs")>]
    member x.``test the Boolean expression modeller`` ast =
        modelBoolExpr ModellerTests.Env ast

    /// Tests for modelling variable lists.
    static member VarLists =
        seq {
            yield (
                new TestCaseData(
                    [ (Type.Bool, "foo")
                      (Type.Bool, "foo") ]
                )
            ).Returns(
                fail <| Starling.Errors.Var.Duplicate "foo"
            ).SetName(
                "disallow var lists with duplicates of same type"
            )
            yield (
                new TestCaseData(
                    [ (Type.Int, "bar")
                      (Type.Bool, "bar") ]
                )
            ).Returns(
                fail <| Starling.Errors.Var.Duplicate "bar" 
            ).SetName(
                "disallow var lists with duplicates of different type"
            )
            yield (
                new TestCaseData(
                    [ (Type.Int, "baz")
                      (Type.Bool, "emp") ]
                )
            ).Returns(
                ok <| Map.ofList [ ("baz", Type.Int) ; ("emp", Type.Bool) ]
            ).SetName(
                "allow var lists with no types"
            )
            yield (
                new TestCaseData([])
            ).Returns(
                ok <| Map.empty
            ).SetName(
                "allow empty var lists"
            )
        }

    /// Tests the creation of var lists.
    [<TestCaseSource("VarLists")>]
    member x.``var lists are checked correctly during mapping`` vl =
        makeVarMap vl

    /// Tests for the atomic primitive modeller.
    /// These use the ticketed lock model.
    static member AtomicPrims =
        seq {
            yield (
                new TestCaseData(
                    Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment)
                )
            ).Returns(
                ok <| IntLoad(Some(LVIdent "t"), LVIdent "ticket", Increment) 
            ).SetName(
                "model a valid integer load as a prim"
            )
        }

    /// Tests the atomic primitive modeller using the ticketed lock.
    [<TestCaseSource("AtomicPrims")>]
    member x.``atomic actions are modelled correctly as prims`` a =
        modelPrimOnAtomic ticketLockModel a

    /// Tests for the command axiom modeller.
    /// These use the ticketed lock model.
    static member CommandAxioms =
        seq {
            yield (
                new TestCaseData(
                    ( { Pre = Multiset.empty()
                        Post = 
                            Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                              Params = [ AExpr (AConst (Unmarked "t")) ] } ] },
                      Atomic(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment)))
                )
            ).Returns(
                ok <| (PAAxiom { Conditions = 
                                    { Pre = Multiset.empty()
                                      Post = 
                                          Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                                            Params = [ AExpr (AConst (Unmarked "t")) ] } ] }
                                 Inner = IntLoad(Some(LVIdent "t"), LVIdent "ticket", Increment) }) 
            ).SetName(
                "model a valid integer load command as an axiom"
            )
        }

    /// Tests the command modeller using the ticketed lock.
    [<TestCaseSource("CommandAxioms")>]
    member x.``commands are modelled correctly as axioms`` (cpair, c) =
        modelAxiomOnCommand ticketLockModel cpair c

    /// Full case studies to model.
    static member Models =
        seq {
            yield (
                new TestCaseData(ticketLockCollated)
            ).Returns(
                ok <| ticketLockModel
            ).SetName(
                "model the ticketed lock"
            )
        }

    /// Tests the whole modelling process.
    [<TestCaseSource("Models")>]
    member x.``case studies are modelled correctly`` col =
        model col
