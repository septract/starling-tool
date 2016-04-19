/// Part of the Starling tool that flattens terms, adding in globals.
module Starling.Flattener

open Starling.Collections
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
    | Uninterpreted (v, d) -> Uninterpreted (funcOfView gs v, d)

(*
 * Whole models
 *)

/// Adds globals to the arguments of all views in a model.
let flatten (mdl: UVModel<PTerm<MViewSet, OView>>) =
    /// Build a function making a list of global arguments, for view assertions.
    let gargs marker = varMapToExprs marker mdl.Globals

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
