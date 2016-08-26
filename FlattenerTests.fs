/// <summary>
///     Part of the Starling tool that flattens terms, adding in globals.
/// </summary>
module Starling.Tests.Flattener

open Starling.Collections
open Starling.Flattener
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic

/// <summary>
///     Tests for <c>Flattener</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Chessie.ErrorHandling
    open Starling.Utils.Testing


    /// <summary>
    ///     NUnit tests for <c>Flattener</c>.
    /// </summary>
    type NUnit () =
        /// The globals environment used in the tests.
        static member Globals : VarMap =
            returnOrFail <| makeVarMap
                [ TypedVar.Int "serving"
                  TypedVar.Int "ticket" ]

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
            (genFlatFuncSeqName : OView -> string) v

        /// Test cases for the full defining-view func converter.
        /// These all use the Globals environment above.
        static member DViewFuncs =
            let ms : DFunc list -> DView = Multiset.ofFlatList >> Multiset.toFlatList
            [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                                { Name = "holdTick"; Params = [ Int "t" ] } ])
                 .Returns({ Name = "v_holdLock_holdTick"
                            Params =
                                [ Int "serving"
                                  Int "ticket"
                                  Int "t" ] } : DFunc)
                .SetName("Convert defining view 'holdLock() * holdTick(t)' to defining func") ]

        /// Tests the viewdef LHS translator.
        [<TestCaseSource("DViewFuncs")>]
        member x.``the defining view func translator works correctly`` (v : DView) =
            v
            |> flattenFuncSeq
                   (NUnit.Globals
                    |> Map.toSeq
                    |> Seq.map (fun (n, t) -> withType t n))

        /// Test cases for the full view func converter.
        /// These all use the Globals environment above.
        static member ViewFuncs =
            let ms : SMVFunc list -> OView = Multiset.ofFlatList >> Multiset.toFlatList
            [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                                { Name = "holdTick"; Params = [ Expr.Int (siBefore "t") ] } ])
                 .Returns({ Name = "v_holdLock_holdTick"
                            Params =
                                [ Expr.Int (siBefore "serving")
                                  Expr.Int (siBefore "ticket")
                                  Expr.Int (siBefore "t") ] })
                .SetName("Convert 'holdLock() * holdTick(t)' to func") ]

        /// Tests the viewdef LHS translator.
        [<TestCaseSource("ViewFuncs")>]
        member x.``the view func translator works correctly`` (v : OView) =
            v
            |> flattenFuncSeq
                   (NUnit.Globals
                    |> Map.toSeq
                    |> Seq.map
                           (function
                            | (x, Type.Int ()) -> x |> siBefore |> Expr.Int
                            | (x, Type.Bool ()) -> x |> sbBefore |> Expr.Bool))
