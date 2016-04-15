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

    /// <summary>
    ///     A typed item.
    /// </summary>
    /// <typeparam name="int">
    ///     The real type of the item when it is 'typed' as <c>Int</c>.
    /// </typeparam>
    /// <typeparam name="bool">
    ///     The real type of the item when it is 'typed' as <c>Bool</c>.
    /// </typeparam>
    type Typed<'int, 'bool> = 
        /// <summary>
        ///    An item of integral 'type'.
        /// </summary>
        | Int of 'int
        | Bool of 'bool

    /// <summary>
    ///     A typed item where every 'type' leads to the same real type.
    /// </summary>
    /// <typeparam name="ty">
    ///     The real type to use for all <c>Typed</c> parameters.
    /// </typeparam>
    type CTyped<'ty> = Typed<'ty, 'ty>

    /// <summary>
    ///     A standalone type annotation.
    /// </summary>
    type Type = CTyped<unit>

    /// <summary>
    ///     A formal parameter.
    /// </summary>
    type Param = CTyped<string>

    /// <summary>
    ///     Extracts the <c>Type</c> of a <c>Typed</c> item.
    /// </summary>
    /// <param name="typed">
    ///     The typed item.
    /// </param>
    /// <returns>
    ///     The item's <c>Type</c>.
    /// </returns>
    let typeOf (typed : Typed<_, _>) : Type =
        match typed with
        | Int _ -> Int ()
        | Bool _ -> Bool ()

    /// <summary>
    ///     Combines a <c>Type</c> with an item to make it
    ///     <c>CTyped</c>.
    /// </summary>
    /// <param name="ty">
    ///     The type to use to mark the item.
    /// </param>
    /// <param name="item">
    ///     The item to be marked.
    /// </param>
    /// <returns>
    ///     A <c>CTyped</c> with <paramref name="item"/> as its value.
    /// </returns>
    let withType (ty : Type) (item : 'a) : CTyped<'a> =
        match ty with
        | Int () -> Int item
        | Bool () -> Bool item

    /// <summary>
    ///     Extracts the value of a <c>CTyped</c> item.
    /// </summary>
    /// <param name="typed">
    ///     The typed item.
    /// </param>
    /// <returns>
    ///     The item's value
    /// </returns>
    let valueOf (typed : CTyped<'a>) : 'a =
        match typed with
        | Int a | Bool a -> a

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
        | Int () -> "int" |> String
        | Bool () -> "bool" |> String

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
    |> List.map valueOf // Extract all names from the list.
    |> findDuplicates
    |> Seq.toList
    |> function
       | [] -> lst
               |> Seq.ofList
               |> Seq.map (fun param -> (valueOf param, typeOf param))
               |> Map.ofSeq |> ok
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
