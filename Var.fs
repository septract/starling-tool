/// Types and functions for variables and variable maps.
module Starling.Core.Var

open Chessie.ErrorHandling

open Starling.Utils


/// <summary>
///     Types for variables and variable maps.
/// </summary>
[<AutoOpen>]
module Types =
    /// An lvalue.
    /// This is given a separate type in case we add to it later.
    type LValue = 
        // TODO(CaptainHayashi): add support for non-variable LValues.
        | LVIdent of string

    /// A variable type.
    type Type = 
        | Int
        | Bool

    /// A variable map.
    type VarMap = Map<string, Type>

    /// A mode for the Fetch atomic action.
    type FetchMode = 
        | Direct // <a = b>
        | Increment // <a = b++>
        | Decrement // <a = b-->

    /// Represents an error when building or converting a variable map.
    type VarMapError = 
        | Duplicate of name : string
        // The variable was not found.
        | NotFound of name : string


/// <summary>
///     Pretty printers for variables.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// Pretty-prints a variable type.
    let printType = 
        function 
        | Type.Int -> "int" |> String
        | Type.Bool -> "bool" |> String

    /// Pretty-prints variable conversion errors.
    let printVarMapError =
        function
        | Duplicate vn -> fmt "variable '{0}' is defined multiple times" [ String vn ]
        | NotFound vn -> fmt "variable '{0}' not in environment" [ String vn ]


/// Flattens a LV to a string.
let rec flattenLV = 
    // TODO(CaptainHayashi): this is completely wrong, but we don't
    // have a semantics for it yet.
    function 
    | LVIdent s -> s

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

/// Looks up a variable record in a variable map.
/// Failures are in terms of VarMapError.
let lookupVar env s = 
    s
    |> tryLookupVar env
    |> failIfNone (NotFound(flattenLV s))

(*
 * Parameter functions
 *)

/// Constructs an integer param.
let ipar x = (Type.Int, x)

/// Constructs a Boolean param.
let bpar x = (Type.Bool, x)
