/// Tests for Starling.Flattener.
module Starling.Tests.Flattener

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Flattener

/// Tests for Starling.Flattener.
type FlattenerTests() =
    /// The globals environment used in the tests.
    static member Globals : VarMap =
        returnOrFail <| makeVarMap
            [ VarDecl.Int "serving"
              VarDecl.Int "ticket" ]

    /// Test cases for the view func renamer.
    static member ViewFuncNamings =
        let ms : SMVFunc list -> OView = Multiset.ofFlatList >> Multiset.toFlatList
        [ TestCaseData(ms [ { Name = "foo"; Params = [] }
                            { Name = "bar_baz"; Params = [] } ])
            .Returns("v_bar__baz_foo") // Remember, multisets sort!
            .SetName("Encode func name of view 'foo() * bar_baz()' as 'v_bar__baz_foo'")
          TestCaseData(ms []).Returns("emp")
            .SetName("Encode func name of view '' as 'emp'") ]

    /// Tests the view predicate name generator.
    [<TestCaseSource("ViewFuncNamings")>]
    member x.``the flattened view name generator generates names correctly`` v =
        let pn : OView -> string = funcNameOfView 
        pn v

    /// Test cases for the full defining-view func converter.
    /// These all use the Globals environment above.
    static member DViewFuncs =
        let ms : DFunc list -> DView = Multiset.ofFlatList >> Multiset.toFlatList
        [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                            { Name = "holdTick"; Params = [ Param.Int "t" ] } ])
             .Returns({ Name = "v_holdLock_holdTick"
                        Params =
                            [ Param.Int "serving"
                              Param.Int "ticket"
                              Param.Int "t" ] })
            .SetName("Convert defining view 'holdLock() * holdTick(t)' to defining func") ]

    /// Tests the viewdef LHS translator.
    [<TestCaseSource("DViewFuncs")>]
    member x.``the defining view func translator works correctly`` (v: DView) =
        v |> funcOfView (FlattenerTests.Globals
                         |> Map.toSeq
                         |> Seq.map (fun (n, t) -> withType t n))

    /// Test cases for the full view func converter.
    /// These all use the Globals environment above.
    static member ViewFuncs =
        let ms : SMVFunc list -> OView = Multiset.ofFlatList >> Multiset.toFlatList
        [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                            { Name = "holdTick"; Params = [ Expr.Int (siUnmarked "t") ] } ])
             .Returns({ Name = "v_holdLock_holdTick"
                        Params =
                            [ Expr.Int (siUnmarked "serving")
                              Expr.Int (siUnmarked "ticket")
                              Expr.Int (siUnmarked "t") ] })
            .SetName("Convert 'holdLock() * holdTick(t)' to func") ]

    /// Tests the viewdef LHS translator.
    [<TestCaseSource("ViewFuncs")>]
    member x.``the view func translator works correctly`` (v: OView) =
        v |> funcOfView (FlattenerTests.Globals
                         |> Map.toSeq
                         |> Seq.map (function
                                     | (x, Type.Int ()) -> x |> siUnmarked |> Expr.Int
                                     | (x, Type.Bool ()) -> x |> sbUnmarked |> Expr.Bool))
