/// Backend for emitting Horn clauses for HSF consumption.

module Starling.HSF

open Starling.Collections
open Starling.Expr
open Starling.Model
open Starling.Horn

/// Generates a predicate name for a view func.
let predNameOfFunc {Name = n} =
    n.Replace("_", "__")

/// Generates a predicate name for a view multiset.
let predNameOfMultiset : Multiset<View> -> string =
    Multiset.toSeq
    >> Seq.map predNameOfFunc
    >> scons "v"
    >> String.concat "_"
