/// Backend for emitting Horn clauses for HSF consumption.

module Starling.HSF

open Starling.Collections
open Starling.Utils
open Starling.Expr
open Starling.Model
open Starling.Horn

(*
 * Predicate renaming
 *)

/// Generates a predicate name for a view func.
let predNameOfFunc {Name = n} = n.Replace("_", "__")

/// Generates a predicate name for a view multiset.
let predNameOfMultiset : Multiset<View> -> string =
    Multiset.toSeq
    >> Seq.map predNameOfFunc
    >> scons "v"
    >> String.concat "_"

(*
 * View def construction
 *)

/// Returns the set of all variable names bound in a viewdef multiset.
let varsInMultiset : Multiset<ViewDef> -> Set<string> =
    Multiset.toSeq
    >> Seq.map (fun v -> Seq.map snd v.Params)
    >> Seq.concat
    >> Set.ofSeq

/// Returns the set of all variable names bound in a view constraint,
/// given the global environment of variables as the second argument.
let varsInConstraint { CViews = vs } =
    Set.union (varsInMultiset vs)
