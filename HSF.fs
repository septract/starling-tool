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
let predNameOfFunc { Name = n } = n.Replace("_", "__")

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

/// Returns the list of all variable names bound in a viewdef multiset.
/// These are guaranteed to be in multiset element order first, and in
/// view definition order per inner func. 
let varsInMultiset : Multiset<ViewDef> -> string list = 
    Multiset.toSeq
    >> Seq.map (fun v -> Seq.map snd v.Params)
    >> Seq.concat
    >> List.ofSeq

/// Checks to ensure all params in a viewdef multiset are arithmetic.
let ensureAllArith : Multiset<ViewDef> -> Result<Multiset<ViewDef>, Error> = 
    Multiset.toSeq
    >> Seq.map (fun { Name = n; Params = ps } -> 
           ps
           |> Seq.map (function 
                  | (Type.Int, _) as x -> ok x
                  | x -> fail <| NonArithParam x)
           |> collect
           |> lift (fun aps -> 
                  { Name = n
                    Params = aps }))
    >> collect
    >> lift Multiset.ofSeq

/// Converts a top-level BoolExpr to a HSF literal.
let topLevelExpr = 
    function 
    | BEq(AExpr x, AExpr y) -> ok <| Eq(x, y)
    | BNot(BEq(AExpr x, AExpr y)) -> ok <| Neq(x, y)
    | BGt(x, y) -> ok <| Gt(x, y)
    | BGe(x, y) -> ok <| Ge(x, y)
    | BLe(x, y) -> ok <| Le(x, y)
    | BLt(x, y) -> ok <| Lt(x, y)
    | x -> fail <| UnsupportedExpr(BExpr x)

/// Constructs the right-hand side of a constraint in HSF.
/// The set of active globals should be passed as env.
let bodyOfConstraint env vs = 
    vs
    |> ensureAllArith
    |> lift (fun avs -> 
           Pred { Name = predNameOfMultiset avs
                  Params = 
                      avs
                      |> varsInMultiset
                      |> List.append (Set.toList env)
                      |> List.map aUnmarked })

/// Constructs a full constraint in HSF.
/// The set of active globals should be passed as env.
/// Some is returned if the constraint is definite; None otherwise.
let hsfConstraint env { CViews = vs; CExpr = ex } = 
    Option.map (fun dex -> 
        lift2 (fun hd bd -> 
            { Head = hd
              Body = [ bd ] }) (topLevelExpr dex) (bodyOfConstraint env vs)) ex
