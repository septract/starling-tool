/// Part of the Starling tool that turns global variables into view parameters.
module Starling.GlobalAdder

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Var

(*
 * View usages
 *)

/// Adds the globals in gs to the argument list of a func.
let addGlobalsToFunc gs f =
    {f with Params = List.append gs f.Params}

/// Adds the globals in gs to a defining view's multiset.
let addGlobalsToView gs view =
    view
    |> Multiset.toList
    |> function
        // Replace emp with an actual func definition.
        | [] -> [addGlobalsToFunc gs {Name = "emp"; Params = []}]
        | xs -> List.map (addGlobalsToFunc gs) xs
    |> Multiset.ofList

/// Adds the globals in gs to the argument list of a guarded view.
let addGlobalsToGuarded gs a =
    {a with Item = addGlobalsToView gs a.Item}

/// Adds the globals in gs to the argument lists of a view assertion.
let addGlobalsToAssertion gs =
    Multiset.map (addGlobalsToGuarded gs)

/// Adds the globals in gs to the argument list of the assertions in a term.
let addGlobalsToTerm gs =
    mapTerm id
            (addGlobalsToAssertion (gs Before))
            (addGlobalsToAssertion (gs After))

(*
 * View definitions
 *)

/// Adds the globals in gs to a defining view.
let addGlobalsToViewDef gs vdf =
    { vdf with View = addGlobalsToView gs vdf.View }

(*
 * Whole models
 *)

/// Adds globals to the arguments of all views in a model.
let globalAdd (mdl: Model<STerm<ViewSet>>) =
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

    {mdl with Axioms = List.map (addGlobalsToTerm gargs) mdl.Axioms
              ViewDefs = List.map (addGlobalsToViewDef gpars) mdl.ViewDefs}
