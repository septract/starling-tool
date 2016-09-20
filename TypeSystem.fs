/// <summary>
///     The Starling type system.
///
///     <para>
///         This module contains the <c>Typed</c> and <c>CTyped</c>
///         types, which implement the core of Starling's type system.
///         Included modules provide type checking, mapping between
///         different instances of <c>Typed</c> types, and convenience
///         functions for extracting types and values from <c>Typed</c>
///         objects.
///     </para>
///
///     <para>
///         In the documentation for this module, we use 'type'
///         to refer to types in the Starling object language, and
///         'meta-type' to refer to types in F#.
///     </para>
/// </summary>
module Starling.Core.TypeSystem

open Chessie.ErrorHandling
open Starling.Utils


/// <summary>
///     A typed item.
/// </summary>
/// <typeparam name="int">
///     The meta-type of the item when it is typed as <c>Int</c>.
/// </typeparam>
/// <typeparam name="bool">
///     The meta-type of the item when it is typed as <c>Bool</c>.
/// </typeparam>
type Typed<'int, 'bool> =
    /// <summary>
    ///    An item of integral type.
    /// </summary>
    | Int of 'int
    | Bool of 'bool
    override this.ToString() =
        match this with
        | Int x -> sprintf "I(%A)" x
        | Bool x -> sprintf "B(%A)" x

/// <summary>
///     A typed item where every type leads to the same meta-type.
/// </summary>
/// <typeparam name="ty">
///     The meta-type to use for all <c>Typed</c> parameters.
/// </typeparam>
type CTyped<'ty> = Typed<'ty, 'ty>

/// <summary>
///     Maps over the contents of a <see cref="CTyped"/>.
/// </summary>
/// <param name="f">
///     The function to map.
/// </param>
/// <returns>
///     A function applying <paramref name="f"/> on a <see cref="CTyped"/>.
/// </returns>
/// <typeparam name="Src">
///     The meta-type of items entering the map.
/// </typeparam>
/// <typeparam name="Dst">
///     The meta-type of items leaving the map.
/// </typeparam>
let mapCTyped (f : 'Src -> 'Dst) : CTyped<'Src> -> CTyped<'Dst> =
    function
    | Int i -> Int (f i)
    | Bool b -> Bool (f b)

/// <summary>
///     A standalone type annotation.
/// </summary>
type Type = CTyped<unit>

/// <summary>
///     The Starling type checker.
/// </summary>
module Check =
    /// <summary>
    ///     Active pattern performing type unification.
    /// </summary>
    let (|UnifyInt|UnifyBool|UnifyFail|)
        = function
          | (Typed.Int x, Typed.Int y) -> UnifyInt (x, y)
          | (Typed.Bool x, Typed.Bool y) -> UnifyBool (x, y)
          | x, y -> UnifyFail (x, y)


/// <summary>
///     Functions for working with <c>Typed</c> values.
/// </summary>
[<AutoOpen>]
module Typed =
    /// <summary>
    ///     Extracts the <c>Type</c> of a <c>Typed</c> item.
    /// </summary>
    /// <param name="typed">
    ///     The typed item.
    /// </param>
    /// <returns>
    ///     The item's <c>Type</c>.
    /// </returns>
    let typeOf : Typed<_, _> -> Type =
        function
        | Bool _ -> Bool ()
        | Int _ -> Int ()

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
    /// <typeparam name="a">
    ///     The meta-type of the item to type.
    /// </typeparam>
    /// <returns>
    ///     A <c>CTyped</c> with <paramref name="item"/> as its value.
    /// </returns>
    let withType (ty : Type) (item : 'a) : CTyped<'a> =
        match ty with
        | Bool () -> Bool item
        | Int () -> Int item

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
    ///     Active pattern splitting a CTyped item into its item and type.
    /// </summary>
    let (|WithType|) x = (valueOf x, typeOf x)


/// <summary>
///     Pretty printers for the type system.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// <summary>
    ///     Pretty-prints a type.
    /// </summary>
    let printType : Type -> Doc =
        function
        | Int () -> "int" |> String
        | Bool () -> "bool" |> String

    /// <summary>
    ///     Pretty-prints a ctyped item.
    ///
    ///     <param>
    ///         The item is printed as, for example, 'int foo',
    ///         where 'int' is the type and 'foo' the result of printing
    ///         the inner item.
    ///     </param>
    /// </summary>
    /// <param name="pItem">
    ///     Pretty printer for the inner item.
    /// </param>
    /// <param name="ctyped">
    ///     The <c>CTyped</c> value to print.
    /// </param>
    /// <typeparam name="item">
    ///     The meta-type of ctyped values.
    /// </typeparam>
    /// <returns>
    ///     A printer <c>Doc</c> printing <paramref name="ctyped"/>.
    /// </returns>
    let printCTyped
      (pItem : 'item -> Doc)
      (ctyped : CTyped<'item>)
      : Doc =
        hsep
            [ printType (typeOf ctyped) |> syntaxIdent
              pItem (valueOf ctyped) ]

    /// <summary>
    ///     Pretty-prints a typed item.
    ///
    ///     <param>
    ///         The item is printed as, for example, 'int foo',
    ///         where 'int' is the type and 'foo' the result of printing
    ///         the inner item.
    ///     </param>
    /// </summary>
    /// <param name="pInt">
    ///     Pretty printer for the inner item when the type is
    ///     <c>Int</c>.
    /// </param>
    /// <param name="pBool">
    ///     Pretty printer for the inner item when the type is
    ///     <c>Bool</c>.
    /// </param>
    /// <typeparam name="int">
    ///     The meta-type of <c>Int</c>-typed values.
    /// </typeparam>
    /// <typeparam name="bool">
    ///     The meta-type of <c>Bool</c>-typed values.
    /// </typeparam>
    /// <returns>
    ///     A function converting <c>Typed</c> items to printer
    ///     <c>Doc</c>s.
    /// </returns>
    let printTyped
      (pInt : 'int -> Doc)
      (pBool : 'bool -> Doc)
      : Typed<'int, 'bool> -> Doc =
        function
        | Int a -> pInt a
        | Bool a -> pBool a
