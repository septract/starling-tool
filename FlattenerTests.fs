/// Tests for Starling.Flattener.
module Starling.Tests.Flattener

open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Flattener

/// Tests for Starling.Flattener.
type FlattenerTests() =
    /// The globals environment used in the tests.
    static member Globals =
        Map.ofList [ ("serving", Type.Int) ; ("ticket", Type.Int) ]

    /// Test cases for the view func renamer.
    static member ViewFuncNamings =
        let ms : VFunc list -> View = Multiset.ofFlatList
        [ TestCaseData(ms [ { Name = "foo"; Params = [] }
                            { Name = "bar_baz"; Params = [] } ])
            .Returns("v_bar__baz_foo") // Remember, multisets sort!
            .SetName("Encode func name of view 'foo() * bar_baz()' as 'v_bar__baz_foo'")
          TestCaseData(ms []).Returns("emp")
            .SetName("Encode func name of view '' as 'emp'") ]

    /// Tests the view predicate name generator.
    [<TestCaseSource("ViewFuncNamings")>]
    member x.``the flattened view name generator generates names correctly`` v =
        let pn : View -> string = funcNameOfView 
        pn v

    /// Test cases for the full defining-view func converter.
    /// These all use the Globals environment above.
    static member DViewFuncs =
        let ms : DFunc list -> DView = Multiset.ofFlatList
        [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                            { Name = "holdTick"; Params = [(Type.Int, "t")] } ])
             .Returns({ Name = "v_holdLock_holdTick"
                        Params =
                            [ (Type.Int, "serving")
                              (Type.Int, "ticket")
                              (Type.Int, "t") ] })
            .SetName("Convert defining view 'holdLock() * holdTick(t)' to defining func") ]

    /// Tests the viewdef LHS translator.
    [<TestCaseSource("DViewFuncs")>]
    member x.``the defining view func translator works correctly`` (v: DView) =
        v |> funcOfView (FlattenerTests.Globals
                         |> Map.toSeq
                         |> Seq.map flipPair)

    /// Test cases for the full view func converter.
    /// These all use the Globals environment above.
    static member ViewFuncs =
        let ms : VFunc list -> View = Multiset.ofFlatList
        [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                            { Name = "holdTick"; Params = [AExpr (aUnmarked "t")] } ])
             .Returns({ Name = "v_holdLock_holdTick"
                        Params =
                            [ AExpr (aUnmarked "serving")
                              AExpr (aUnmarked "ticket")
                              AExpr (aUnmarked "t") ] })
            .SetName("Convert 'holdLock() * holdTick(t)' to func") ]

    /// Tests the viewdef LHS translator.
    [<TestCaseSource("ViewFuncs")>]
    member x.``the view func translator works correctly`` (v: View) =
        v |> funcOfView (FlattenerTests.Globals
                         |> Map.toSeq
                         |> Seq.map (function
                                     | (x, Type.Int) -> x |> aUnmarked |> AExpr
                                     | (x, Type.Bool) -> x |> bUnmarked |> BExpr))
