/// <summary>
///     Tests for <c>Starling.Tests.Modeller</c>.
/// </summary>
module Starling.Tests.Modeller

open NUnit.Framework
open Starling
open Starling.Collections
open Starling.Core
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Lang.AST
open Starling.Core.Model
open Starling.Lang.Modeller
open Starling.Tests.Studies

/// Wrapper for search modeller tests.
/// Mainly exists to persuade nUnit to use the correct types.
type SearchViewDefEntry =
    { Search : int option
      InitDefs : ViewDefiner<BoolExpr<Sym<Var>> option> }

/// Tests for the modeller.
type ModellerTests() =
    /// View prototypes for the ticket lock modeller.
    static member TicketLockProtos : FuncDefiner<unit> =
        FuncDefiner.ofSeq
            [ (func "holdLock" [], ())
              (func "holdTick" [ Int "t" ], ()) ]

    /// Sample environment used in expression modelling tests.
    static member Env =
        Map.ofList [ ("foo", Type.Int ())
                     ("bar", Type.Int ())
                     ("baz", Type.Bool ())
                     ("emp", Type.Bool ()) ]

    // Method context containing a small amount of variables.
    static member Context =
        { ViewProtos = ModellerTests.TicketLockProtos
          SharedVars = Map.empty
          ThreadVars = ModellerTests.Env }

    // Method context containing all of the ticket lock variables.
    static member TicketLockContext =
        { ViewProtos = ModellerTests.TicketLockProtos
          SharedVars = ticketLockModel.Globals
          ThreadVars = ticketLockModel.Locals }

    static member EmptyCView : CView = Multiset.empty

    /// <summary>
    ///     Test cases for checking view modelling on correct view exprs.
    /// </summary>
    static member ViewExprsGood =
        [ TestCaseData(View.Unit)
             .Returns(Some (ModellerTests.EmptyCView))
             .SetName("Modelling the unit view returns the empty multiset")
          TestCaseData(afunc "holdLock" [] |> View.Func)
             .Returns(Some (Multiset.singleton (CFunc.Func (vfunc "holdLock" []))))
             .SetName("Modelling a valid single view returns a singleton multiset")
        ]

    /// <summary>
    ///     Tests view modelling on correct view exprs.
    /// </summary>
    [<TestCaseSource("ViewExprsGood")>]
    member x.``View modelling on correct view expressions succeeds`` vex =
        vex
        |> modelCView ModellerTests.Context
        |> okOption


    /// <summary>
    ///     Test cases for checking view modelling on incorrect view exprs.
    /// </summary>
    static member ViewExprsBad =
        [ TestCaseData(afunc "badfunc" [] |> View.Func)
             .Returns(Some [NoSuchView "badfunc"])
             .SetName("Modelling an unknown single view returns an error")
          TestCaseData(afunc "holdTick" [] |> View.Func)
             .Returns(Some [LookupError ("holdTick", CountMismatch(0, 1))])
             .SetName("Modelling a single view with bad parameter count returns an error")
          TestCaseData(afunc "holdTick" [freshNode Expression'.True] |> View.Func)
             .Returns(Some [ LookupError
                                 ("holdTick",
                                  Error.TypeMismatch
                                      (Int "t", Type.Bool ()))])
             .SetName("Modelling a single view with bad parameter type returns an error") ]

    /// <summary>
    ///     Tests view modelling on correct view exprs.
    /// </summary>
    [<TestCaseSource("ViewExprsBad")>]
    member x.``View modelling on incorrect view expressions fails`` vex =
        vex
        |> modelCView ModellerTests.Context
        |> failOption


    /// Arithmetic expression modelling tests.
    static member ArithmeticExprs =
        [ TestCaseData(freshNode <| BopExpr(Add, freshNode <| BopExpr(Mul, freshNode <| Num 1L, freshNode <| Num 2L), freshNode <| Num 3L))
              .Returns(Some (AAdd [ AMul [ AInt 1L ; AInt 2L ] ; AInt 3L ]
                             : IntExpr<Sym<Var>>))
              .SetName("model (1 * 2) + 3") ]

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("ArithmeticExprs")>]
    member x.``test the arithmetic expression modeller`` ast =
        modelIntExpr ModellerTests.Env id ast |> okOption


    /// Boolean expression modelling tests.
    /// These all use the ticket lock model.
    static member BooleanExprs =
        [ TestCaseData(freshNode <| BopExpr(And, freshNode <| BopExpr(Or, freshNode True, freshNode True), freshNode False))
              .Returns(Some (BFalse : BoolExpr<Sym<Var>>))
              .SetName("model and simplify (true || true) && false") ]

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("BooleanExprs")>]
    member x.``test the Boolean expression modeller`` ast =
        ast
        |> modelBoolExpr ModellerTests.Env id
        |> okOption


    /// Tests for modelling bad variable lists.
    static member BadVarLists =
        [ TestCaseData([ (CTyped.Bool "foo")
                         (CTyped.Bool "foo") ]).Returns(Some <| [ VarMapError.Duplicate "foo" ])
              .SetName("disallow var lists with duplicates of same type")

          TestCaseData([ (CTyped.Int "bar")
                         (CTyped.Bool "bar") ]).Returns(Some <| [ VarMapError.Duplicate "bar" ])
              .SetName("disallow var lists with duplicates of different type") ]


    /// Tests the creation of var lists.
    [<TestCaseSource("BadVarLists")>]
    member x.``invalid var lists are rejected during mapping`` vl = makeVarMap vl |> failOption

    /// Tests for modelling valid variable lists.
    static member VarLists =
        let emp : CTyped<string> list = []
        let empm : VarMap = Map.empty
        [ TestCaseData([ (CTyped.Int "baz")
                         (CTyped.Bool "emp") ])
              .Returns(Some <| Map.ofList [ ("baz", Type.Int ())
                                            ("emp", Type.Bool ()) ])
              .SetName("allow var lists with no duplicate variables")
          TestCaseData(emp).Returns(Some <| empm).SetName("allow empty var lists") ]

    /// Tests the creation of var lists.
    [<TestCaseSource("VarLists")>]
    member x.``valid var lists are accepted during mapping`` (vl: TypedVar list) =
        makeVarMap vl |> okOption

    /// Constructs a Prim of the correct type to come out of a modeller.
    static member mprim (cmd : Command) : PartCmd<ViewExpr<CView>> = Prim cmd

    /// Constructs a Command<View> containing one atomic.
    static member prim (ac : Atomic) : Command<ViewExpr<Starling.Lang.AST.Types.View>> =
        freshNode
        <| Command'.Prim { PreAssigns = []
                           Atomics = [ ac ]
                           PostAssigns = [] }

    /// Tests for the atomic primitive modeller.
    /// These use the ticket lock model.
    static member AtomicPrims =
        [ TestCaseData(freshNode <| Fetch(LVIdent "t", freshNode <| LV(LVIdent "ticket"), Increment))
            .Returns(Some <|
                         command "!ILoad++"
                                 [ Int "t"; Int "ticket" ] 
                                 [ "ticket" |> siBefore |> SMExpr.Int ] )
            .SetName("model a valid integer load as a prim") ]

    /// Tests the atomic primitive modeller using the ticket lock.
    [<TestCaseSource("AtomicPrims")>]
    member x.``atomic primitives are modelled correctly as prims`` a =
        a
        |> modelAtomic ModellerTests.TicketLockContext
        |> okOption



    /// Tests for the command axiom modeller.
    /// These use the ticket lock model.
    static member CommandAxioms =
        [ TestCaseData(ModellerTests.prim(freshNode <| Fetch(LVIdent "t",
                                                freshNode <| LV(LVIdent "ticket"),
                                                Increment)))
            .Returns(ModellerTests.mprim
                         [ command "!ILoad++" [Int "t"; Int "ticket"] [ "ticket" |> siBefore |> SMExpr.Int ]]
                     |> Some)
            .SetName("model a valid integer load command as an axiom") ]

    /// Tests the command modeller using the ticket lock.
    [<TestCaseSource("CommandAxioms")>]
    member x.``commands are modelled correctly as part-commands`` c =
        c
        |> modelCommand ModellerTests.TicketLockContext
        |> okOption


    /// Type-constraining builder for viewdef sets.
    static member viewDefSet
      (vs : (View.Types.DView * BoolExpr<Sym<Var>> option) seq)
      : Set<View.Types.DView * BoolExpr<Sym<Var>> option> =
        Set.ofSeq vs

    /// Type-constraining builder for indefinite viewdef sets.
    static member indefinites (vs : View.Types.DView seq)
      : Set<View.Types.DView * BoolExpr<Sym<Var>> option> =
        vs
        |> Seq.map (fun v -> (v, None))
        |> ModellerTests.viewDefSet

    /// Tests for the search modeller.
    /// These use TicketLockProtos.
    static member SearchViewDefs =
        [ TestCaseData({ Search = None; InitDefs = []})
             .Returns(ModellerTests.indefinites [])
             .SetName("Searching for no viewdefs does not change an empty viewdef set")
          TestCaseData({ Search = None; InitDefs = ticketLockViewDefs })
             .Returns(ModellerTests.viewDefSet ticketLockViewDefs)
             .SetName("Searching for no viewdefs does not change a full viewdef set")
          TestCaseData({ Search = Some 0; InitDefs = []})
             .Returns(ModellerTests.indefinites [ [] ] )
             .SetName("Searching for size-0 viewdefs adds emp to an empty viewdef set")
          TestCaseData({ Search = Some 0; InitDefs = ticketLockViewDefs })
             .Returns(ModellerTests.viewDefSet ticketLockViewDefs)
             .SetName("Searching for size-0 viewdefs does not change a full viewdef set")
          TestCaseData({ Search = Some 1; InitDefs = [] })
             .Returns(ModellerTests.indefinites
                          [ []
                            [ func "holdLock" [] ]
                            [ func "holdTick" [ Int "t0" ] ] ] )
             .SetName("Searching for size-1 viewdefs yields viewdefs for emp and the view prototypes")
          TestCaseData({ Search = Some 2; InitDefs = [] })
             .Returns(ModellerTests.indefinites
                          [ []
                            [ func "holdLock" [] ]
                            [ func "holdLock" []
                              func "holdLock" [] ]
                            [ func "holdLock" []
                              func "holdTick" [ Int "t0" ] ]
                            [ func "holdTick" [ Int "t0" ] ]
                            [ func "holdTick" [ Int "t0" ]
                              func "holdTick" [ Int "t1" ] ] ] )
             .SetName("Searching for size-2 viewdefs yields the correct views") ]

    /// Tests viewdef searches.
    [<TestCaseSource("SearchViewDefs")>]
    member x.``viewdef searches are carried out correctly`` svd =
        addSearchDefs ModellerTests.TicketLockProtos svd.Search svd.InitDefs
        |> ViewDefiner.toSeq
        |> Set.ofSeq

    /// Full case studies to model.
    static member Models =
        [ TestCaseData(ticketLockCollated).Returns(Some ticketLockModel).SetName("model the ticket lock") ]

    /// Tests the whole modelling process.
    [<TestCaseSource("Models")>]
    member x.``case studies are modelled correctly`` col = model col |> okOption
