module Starling.Tests.Modeller

open NUnit.Framework
open Starling
open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Core.Model
open Starling.Lang.AST
open Starling.Lang.Modeller
open Starling.Tests.Studies

/// Tests for the modeller.
type ModellerTests() =

    /// Sample environment used in expression modelling tests.
    static member Env =
        Map.ofList [ ("foo", Type.Int)
                     ("bar", Type.Int)
                     ("baz", Type.Bool)
                     ("emp", Type.Bool) ]

    /// Arithmetic expression modelling tests.
    static member ArithmeticExprs =
        [ TestCaseData(Bop(Add, Bop(Mul, Int 1L, Int 2L), Int 3L)).Returns(Some <| AAdd [ AMul [ AInt 1L
                                                                                                 AInt 2L ]
                                                                                          AInt 3L ])
            .SetName("model (1 * 2) + 3") ]

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("ArithmeticExprs")>]
    member x.``test the arithmetic expression modeller`` ast = modelArithExpr ModellerTests.Env ast |> okOption

    /// Boolean expression modelling tests.
    /// These all use the ticketed lock model.
    static member BooleanExprs =
        [ TestCaseData(Bop(And, Bop(Or, True, True), False)).Returns(Some BFalse)
            .SetName("model and simplify (true || true) && false") ]

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("BooleanExprs")>]
    member x.``test the Boolean expression modeller`` ast =
        ast
        |> modelBoolExpr ModellerTests.Env
        |> okOption

    /// Tests for modelling bad variable lists.
    static member BadVarLists =
        [ TestCaseData([ (Type.Bool, "foo")
                         (Type.Bool, "foo") ]).Returns(Some <| [ Starling.Errors.Var.Duplicate "foo" ])
              .SetName("disallow var lists with duplicates of same type")

          TestCaseData([ (Type.Int, "bar")
                         (Type.Bool, "bar") ]).Returns(Some <| [ Starling.Errors.Var.Duplicate "bar" ])
              .SetName("disallow var lists with duplicates of different type") ]


    /// Tests the creation of var lists.
    [<TestCaseSource("BadVarLists")>]
    member x.``invalid var lists are rejected during mapping`` vl = makeVarMap vl |> failOption

    /// Tests for modelling valid variable lists.
    static member VarLists =
        let emp : (Type * string) list = []
        let empm : VarMap = Map.empty
        [ TestCaseData([ (Type.Int, "baz")
                         (Type.Bool, "emp") ])
              .Returns(Some <| Map.ofList [ ("baz", Type.Int)
                                            ("emp", Type.Bool) ])
              .SetName("allow var lists with no duplicate variables")
          TestCaseData(emp).Returns(Some <| empm).SetName("allow empty var lists") ]

    /// Tests the creation of var lists.
    [<TestCaseSource("VarLists")>]
    member x.``valid var lists are accepted during mapping`` (vl: (Type * string) list) =
        makeVarMap vl |> okOption

    /// Tests for the atomic primitive modeller.
    /// These use the ticketed lock model.
    static member AtomicPrims =
        [ TestCaseData(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment))
            .Returns(Some <| func "!ILoad++" ["t" |> aBefore |> AExpr; "t" |> aAfter |> AExpr
                                              "ticket" |> aBefore |> AExpr; "ticket" |> aAfter |> AExpr])
            .SetName("model a valid integer load as a prim") ]

    /// Tests the atomic primitive modeller using the ticketed lock.
    [<TestCaseSource("AtomicPrims")>]
    member x.``atomic actions are modelled correctly as prims`` a = modelAtomic ticketLockModel.Globals ticketLockModel.Locals a |> okOption

    /// Constructs a Prim of the correct type to come out of a modeller.
    static member mprim (vf : VFunc) : PartCmd<CView> = Prim vf

    /// Tests for the command axiom modeller.
    /// These use the ticketed lock model.
    static member CommandAxioms =
        [ TestCaseData(Atomic(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment)))
            .Returns(ModellerTests.mprim
                         (func "!ILoad++" ["t" |> aBefore |> AExpr; "t" |> aAfter |> AExpr
                                           "ticket" |> aBefore |> AExpr; "ticket" |> aAfter |> AExpr])
                     |> Some)
            .SetName("model a valid integer load command as an axiom") ]

    /// Tests the command modeller using the ticketed lock.
    [<TestCaseSource("CommandAxioms")>]
    member x.``commands are modelled correctly as part-commands`` c =
        modelCommand ticketLockModel.Globals ticketLockModel.Locals c |> okOption

    /// Full case studies to model.
    //static member Models =
    //    [ TestCaseData(ticketLockCollated).Returns(Some ticketLockModel).SetName("model the ticketed lock") ]

    /// Tests the whole modelling process.
    //[<TestCaseSource("Models")>]
    //member x.``case studies are modelled correctly`` col = model col |> okOption
    
