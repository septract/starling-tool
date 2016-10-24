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
/// <typeparam name="Int">
///     The meta-type of the item when it is typed as <c>Int</c>.
/// </typeparam>
/// <typeparam name="Bool">
///     The meta-type of the item when it is typed as <c>Bool</c>.
/// </typeparam>
/// <typeparam name="Array">
///     The meta-type of the item when it is typed as <c>Array</c>.
/// </typeparam>
type Typed<'Int, 'Bool, 'Array> =
    /// <summary>
    ///    An item of integral type.
    /// </summary>
    | Int of 'Int
    /// <summary>
    ///    An item of Boolean type.
    /// </summary>
    | Bool of 'Bool
    /// <summary>
    ///    An item of array type, annotated by the type of the array element
    ///    and an optional length.
    /// </summary>
    | Array of eltype : Typed<unit, unit, unit>
             * length : int option
             * value  : 'Array
    override this.ToString() =
        match this with
        | Int x -> sprintf "I(%A)" x
        | Bool x -> sprintf "B(%A)" x
        | Array (eltype, length, x) -> sprintf "A<%A, %A>(%A)" eltype length x

/// <summary>
///     A typed item where every type leads to the same meta-type.
/// </summary>
/// <typeparam name="T">
///     The meta-type to use for all <c>Typed</c> parameters.
/// </typeparam>
type CTyped<'T> = Typed<'T, 'T, 'T>

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
    | Array (eltype, length, a) -> Array (eltype, length, f a)

/// <summary>
///     A standalone type annotation.
/// </summary>
type Type = CTyped<unit>

/// <summary>
///     Checks whether two types are compatible.
/// </summary>
/// <param name="x">The first type to check.</param>
/// <param name="y">The second type to check.</param>
/// <returns>
///     True if <paramref name="x"/> can be made compatible with
///     <paramref name="y"/>, or vice versa; false otherwise.
/// </returns>
let typesCompatible (x : Type) (y : Type) : bool =
    (* Technically, if this was proper unification, we'd want to return a
       record of the substitutions made. *)
    match (x, y) with
    (* Arrays are compatible when their element types are compatible and their
       lengths are not both defined as contradictory values. *)
    | (Type.Array (ex, Some _ , ()), Type.Array (ey, None   , ()))
    | (Type.Array (ex, None   , ()), Type.Array (ey, Some _ , ()))
    | (Type.Array (ex, None   , ()), Type.Array (ey, None   , ())) ->
        ex = ey
    | (Type.Array (ex, Some lx, x), Typed.Array (ey, Some ly, y)) ->
        ex = ey && lx = ly
    // For primitive types, structural equality suffices.
    | x, y -> x = y


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
    let typeOf : Typed<_, _, _> -> Type =
        function
        | Bool _ -> Bool ()
        | Int _ -> Int ()
        | Array (eltype, length, _) -> Array (eltype, length, ())

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
        | Array (eltype, length, ()) -> Array (eltype, length, item)

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
        | Int a | Bool a | Array (_, _, a) -> a

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
    let rec printType : Type -> Doc =
        function
        | Int () -> "int" |> String
        | Bool () -> "bool" |> String
        | Array (eltype, len, ()) ->
            parened
                (String "array"
                 <+> printType eltype
                 <+> maybe (String "?") printInt len)

    /// <summary>
    ///     Pretty-prints a typed item.
    ///
    ///     <para>
    ///         The item is printed as, for example, '(int foo)',
    ///         where 'int' is the type and 'foo' the result of printing
    ///         the inner item.  If the pretty printer returns a no-op, then
    ///         no extra whitespace is generated.
    ///     </para>
    /// </summary>
    /// <param name="pInt">
    ///     Pretty printer for the inner item when the type is
    ///     <c>Int</c>.
    /// </param>
    /// <param name="pBool">
    ///     Pretty printer for the inner item when the type is
    ///     <c>Bool</c>.
    /// </param>
    /// <param name="typed">The typed item to print.</typed>
    /// <typeparam name="Int">
    ///     The meta-type of <c>Int</c>-typed values.
    /// </typeparam>
    /// <typeparam name="Bool">
    ///     The meta-type of <c>Bool</c>-typed values.
    /// </typeparam>
    /// <returns>
    ///     A <see cref="Doc"/> capturing the typed value.
    /// </returns>
    let printTyped
      (pInt : 'Int -> Doc)
      (pBool : 'Bool -> Doc)
      (pArray : Type -> int option -> 'Array -> Doc)
      (typed : Typed<'Int, 'Bool, 'Array>) : Doc =
        let typeDoc = printType (typeOf typed)

        let valDoc =
            match typed with
            | Int a -> pInt a
            | Bool a -> pBool a
            | Array (eltype, length, a) -> pArray eltype length a

        let sexprContents =
            match valDoc with
            | Nop -> []
            | doc -> [ doc ]

        parened (hsep (typeDoc::sexprContents))

    /// <summary>
    ///     Pretty-prints a ctyped item.
    ///
    ///     <para>
    ///         See <see cref="printTyped"/> for more information.
    ///     </para>
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
    let printCTyped (pItem : 'item -> Doc) (ctyped : CTyped<'item>) : Doc =
        printTyped pItem pItem (fun _ _ -> pItem) ctyped
