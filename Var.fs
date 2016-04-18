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

    /// <summary>
    ///     A table of mapping functions from one <c>Typed</c> type to another.
    /// </summary>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    /// </typeparam>
    [<NoComparison>]
    [<NoEquality>]
    type TypeMapper<'srcInt, 'srcBool, 'dstInt, 'dstBool> =
        { /// <summary>
          ///     Mapping function for integers.
          /// </summary>
          I: 'srcInt -> 'dstInt
          /// <summary>
          ///     Mapping function for Booleans.
          /// </summary>
          B: 'srcBool -> 'dstBool }

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


/// <summary>
///     Functions for dealing with <c>TypeMapper</c>s.
/// </summary>
module TypeMapper =
    /// <summary>
    ///     Runs a <c>TypeMapper</c> on a <c>Typed</c> value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>TypeMapper</c> to run.
    /// </param>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A function mapping over a <c>Typed</c> value with
    ///     <paramref name="tm"/>.
    /// </returns>
    let map
      (tm : TypeMapper<'srcInt, 'srcBool, 'dstInt, 'dstBool>)
      : (Typed<'srcInt, 'srcBool> -> Typed<'dstInt, 'dstBool>) =
        function
        | Typed.Int i -> i |> tm.I |> Typed.Int
        | Typed.Bool i -> i |> tm.B |> Typed.Bool

    /// <summary>
    ///     Runs a <c>TypeMapper</c> on an integral value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>TypeMapper</c> to run.
    /// </param>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A function mapping over an integral value (ie, the
    ///     <c>srcInt</c> and <c>dstInt</c> types) with
    ///     <paramref name="tm"/>.
    /// </returns>
    let mapInt
      (tm : TypeMapper<'srcInt, _, 'dstInt, _>)
      : 'srcInt -> 'dstInt =
        tm.I

    /// <summary>
    ///     Runs a <c>TypeMapper</c> on a Boolean value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>TypeMapper</c> to run.
    /// </param>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A function mapping over a Boolean value (ie, the
    ///     <c>srcBool</c> and <c>dstBool</c> types) with
    ///     <paramref name="tm"/>.
    /// </returns>
    let mapBool
      (tm : TypeMapper<_, 'srcBool, _, 'dstBool>)
      : 'srcBool -> 'dstBool =
        tm.B

    /// <summary>
    ///     Constructs a <c>TypeMapper</c>.
    /// </summary>
    /// <param name="iFun">
    ///     The function to apply on integral values.
    /// </param>
    /// <param name="bFun">
    ///     The function to apply on Boolean values.
    /// </param>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A <c>TypeMapper</c> using <paramref name="iFun"/> and
    ///     <paramref name="bFun"/>.
    /// </returns>
    let make
      (iFun : 'srcInt -> 'dstInt)
      (bFun : 'srcBool -> 'dstBool)
      : TypeMapper<'srcInt, 'srcBool, 'dstInt, 'dstBool> =
        { I = iFun ; B = bFun }

    /// <summary>
    ///     Constructs a <c>TypeMapper</c> over <c>CTyped</c>.
    /// </summary>
    /// <param name="f">
    ///     The function to apply on all values.
    /// </param>
    /// <typeparam name="src">
    ///     The type of values entering the map.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The type of values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A <c>TypeMapper</c> using <paramref name="f"/>.
    /// </returns>
    let cmake
      (f : 'src -> 'dst)
      : TypeMapper<'src, 'src, 'dst, 'dst> =
        make f f

    /// <summary>
    ///     Composes two <c>TypeMapper</c>s.
    /// </summary>
    /// <param name="f">
    ///     The <c>TypeMapper</c> to apply first.
    /// </param>
    /// <param name="g">
    ///     The <c>TypeMapper</c> to apply second.
    /// </param>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="fInt">
    ///     The type of <c>Int</c>-typed values after
    ///     <paramref name="f" />.
    /// </typeparam>
    /// <typeparam name="fBool">
    ///     The type of <c>Bool</c>-typed values after
    ///     <paramref name="f" />.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A <c>TypeMapper</c> composing <paramref name="f"/> and
    ///     <paramref name="g"/> left-to-right.
    /// </returns>
    let compose
      (f : TypeMapper<'srcInt, 'srcBool, 'fInt, 'fBool>)
      (g : TypeMapper<'fInt, 'fBool, 'dstInt, 'dstBool>)
      : TypeMapper<'srcInt, 'srcBool, 'dstInt, 'dstBool> =
        { I = f.I >> g.I
          B = f.B >> g.B }


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
