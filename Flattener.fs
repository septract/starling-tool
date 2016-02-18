/// Part of the Starling tool that flattens terms, adding in globals.
module Starling.Flattener

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Var


(*
 * View-to-func flattening.
 *)

/// Extracts a sequence of all of the parameters in a view in order.
let paramsOfView ms =
    ms
    |> Multiset.toSeq
    |> Seq.map (fun v -> v.Params)
    |> Seq.concat

/// Constructs a (hopefully) unique name for a func encompassing a view.
let funcNameOfView ms =
    ms
    |> Multiset.toSeq
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

/// Adds the globals in gs to the argument list of a guarded view.
let addGlobalsToGuarded gs {Cond = c; Item = i} =
    { Cond = c; Item = funcOfView gs i }

/// Adds the globals in gs to the argument lists of a view assertion.
let addGlobalsToViewSet gs =
    Multiset.map (addGlobalsToGuarded gs)

/// Adds the globals in gs to the argument list of the assertions in a term.
let addGlobalsToTerm gs =
    mapTerm id
            (addGlobalsToViewSet (gs Before))
            (funcOfView (gs After))

(*
 * View definitions
 *)

/// Adds the globals in gs to a defining view.
let addGlobalsToViewDef gs {View = v; Def = d} =
    { View = funcOfView gs v; Def = d }


(*
 * Whole models
 *)

/// Adds globals to the arguments of all views in a model.
let flatten (mdl: Model<STerm<ViewSet, View>, DView>) =
    /// Build a function making a list of global arguments, for view assertions.
    let gargs marker = 
        mdl.Globals
        |> Map.toSeq
        |> Seq.map
            (fun (name, ty) ->
                name
                |> marker
                |> match ty with
                   | Type.Int -> AConst >> AExpr
                   | Type.Bool -> BConst >> BExpr)
        |> List.ofSeq

    /// Build a list of global parameters, for view definitions.
    let gpars =
        mdl.Globals
        |> Map.toSeq
        |> Seq.map flipPair
        |> List.ofSeq

    {Globals = mdl.Globals
     Locals = mdl.Locals
     Axioms = List.map (addGlobalsToTerm gargs) mdl.Axioms
     ViewDefs = List.map (addGlobalsToViewDef gpars) mdl.ViewDefs
     Semantics = mdl.Semantics}
