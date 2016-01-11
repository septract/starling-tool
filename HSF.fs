/// Backend for emitting Horn clauses for HSF consumption.

module Starling.HSF

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Var
open Starling.Expr
open Starling.Model
open Starling.Horn
open Starling.Errors.Horn

(*
 * Predicate renaming
 *)

/// Generates a predicate name for a view func.
let predNameOfFunc {Name = n} = n.Replace("_", "__")

/// Generates a predicate name for a view multiset.
let predNameOfMultiset ms =
    ms
    |> Multiset.toSeq
    |> Seq.map predNameOfFunc
    |> scons "v"
    |> String.concat "_"

(*
 * View def construction
 *)

/// Returns the set of all variable names bound in a viewdef multiset.
let varsInMultiset : Multiset<ViewDef> -> Set<string> =
    Multiset.toSeq
    >> Seq.map (fun v -> Seq.map snd v.Params)
    >> Seq.concat
    >> Set.ofSeq

/// Checks to ensure all params in a viewdef multiset are arithmetic.
let ensureAllArith : Multiset<ViewDef> -> Result<Multiset<ViewDef>, Error> =
    Multiset.toSeq
    >> Seq.map (fun {Name = n; Params = ps} -> 
                    ps
                    |> Seq.map (function
                                | (Type.Int, _) as x -> ok x
                                | x -> fail <| NonArithParam x)
                    |> collect
                    |> lift (fun aps -> {Name = n; Params = aps}))
    >> collect
    >> lift Multiset.ofSeq

/// Constructs the left-hand side of a constraint in HSF.
/// The set of active globals should be passed as env.
let headOfConstraint env { CViews = vs } =
    vs
    |> ensureAllArith
    |> lift (fun avs -> Pred { Name = predNameOfMultiset avs 
                               Params = Set.union env (varsInMultiset avs) |> Set.toList |> List.map aUnmarked })

