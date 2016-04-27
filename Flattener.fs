/// <summary>
///     Part of the Starling tool that flattens terms, adding in globals.
/// </summary>
module Starling.Flattener

open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Var
open Starling.Core.GuardedView


(*
 * View-to-func flattening.
 *)

/// Extracts a sequence of all of the parameters in a view in order.
let paramsOfView ms =
    ms
    |> Seq.map (fun v -> v.Params)
    |> Seq.concat

/// Constructs a (hopefully) unique name for a func encompassing a view.
let funcNameOfView ms =
    ms
    // These two steps are to ensure we don't capture an existing name.
    |> Seq.map (fun { Name = n } -> n.Replace("_", "__"))
    |> scons "v"
    |> String.concat "_"
    |> (fun s -> if s = "v" then "emp" else s)

/// Constructs a Func from a View, given a set of active globals in the
/// appropriate format for appending into the func's parameter list.
/// and some transformer from the parameters to expressions.
let funcOfView globals view =
    { Name = view |> funcNameOfView
      Params = view |> paramsOfView |> Seq.append globals |> List.ofSeq }

(*
 * View usages
 *)

/// Adds the globals in gs to the argument lists of a view assertion.
let addGlobalsToViewSet gs = mapItems (funcOfView gs)

/// Adds the globals in gs to the argument list of the assertions in a term.
let addGlobalsToTerm gs _ =
    mapTerm id
            (addGlobalsToViewSet (gs Before))
            (funcOfView (gs After))

(*
 * View definitions
 *)

/// Adds the globals in gs to a defining view.
let addGlobalsToViewDef gs =
    function
    | Definite (v, d) -> Definite (funcOfView gs v, d)
    | Indefinite v -> Indefinite (funcOfView gs v)

(*
 * Whole models
 *)

/// Adds globals to the arguments of all views in a model.
let flatten (mdl: UVModel<PTerm<SMViewSet, OView>>) =
    /// Build a function making a list of global arguments, for view assertions.
    let gargs marker = varMapToExprs (marker >> Reg) mdl.Globals

    /// Build a list of global parameters, for view definitions.
    let gpars =
        mdl.Globals
        |> Map.toSeq
        |> Seq.map (fun (name, ty) -> withType ty name)
        |> List.ofSeq

    {Globals = mdl.Globals
     Locals = mdl.Locals
     Axioms = Map.map (addGlobalsToTerm gargs) mdl.Axioms
     ViewDefs = List.map (addGlobalsToViewDef gpars) mdl.ViewDefs
     Semantics = mdl.Semantics}


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
            v |> funcOfView (NUnit.Globals
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
        member x.``the view func translator works correctly`` (v: OView) =
            v |> funcOfView (NUnit.Globals
                             |> Map.toSeq
                             |> Seq.map (function
                                         | (x, Type.Int ()) -> x |> siBefore |> Expr.Int
                                         | (x, Type.Bool ()) -> x |> sbBefore |> Expr.Bool))
