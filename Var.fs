/// Types and functions for variables and variable maps.
module Starling.Var

open Chessie.ErrorHandling
open Starling.Errors.Var

(*
 * LValues
 *
 * TODO(CaptainHayashi): add support for non-variable LValues.
 *)

/// An lvalue.
/// This is given a separate type in case we add to it later.
type LValue = 
    | LVIdent of string

/// Flattens a LV to a string.
let rec flattenLV = 
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    function 
    | LVIdent s -> s

(*
 * Types
 *)

/// A variable type.
type Type = 
    | Int
    | Bool

(*
 * Variable records
 *)

/// A variable map.
type VarMap = Map<string, Type>

/// Makes a variable map from a list of type-name pairs.
let makeVarMap lst = 
    lst
    |> List.map snd // Extract all names from the list.
    |> findDuplicates
    |> Seq.toList
    |> function
       | [] -> lst |> Seq.ofList |> Seq.map (fun (ty, name) -> (name, ty)) |> Map.ofSeq |> ok
       | ds -> List.map Duplicate ds |> Bad

/// Tries to combine two variable maps.
/// Fails if the environments are not disjoint.
/// Failures are in terms of VarMapError.
let combineMaps (a : VarMap) (b : VarMap) = 
    Map.fold (fun (sR : Result<VarMap, VarMapError>) name var -> 
        trial { 
            let! s = sR
            if s.ContainsKey name then return! (fail (Duplicate name))
            else return (s.Add(name, var))
        }) (ok a) b

/// Tries to look up a variable record in a variable map.
/// Failures are in terms of Some/None.
let tryLookupVar env = function 
    | LVIdent s -> Map.tryFind s env

//| _ -> LEBadLValue lvalue |> fail
/// Looks up a variable record in a variable map.
/// Failures are in terms of VarMapError.
let lookupVar env s = 
    s
    |> tryLookupVar env
    |> failIfNone (NotFound(flattenLV s))

(*
 * Fetch modes
 *)

/// A mode for the Fetch atomic action.
type FetchMode = 
    | Direct // <a = b>
    | Increment // <a = b++>
    | Decrement // <a = b-->

(*
 * Parameter functions
 *)

/// Constructs an integer param.
let ipar x = (Type.Int, x)

/// Constructs a Boolean param.
let bpar x = (Type.Bool, x)
