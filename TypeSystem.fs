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
///     A subtype definition.
/// </summary>
type Subtype =
    | /// <summary>The subtype of this item is not fixed yet.</summary>
      Indef
    | /// <summary>This item has the 'normal' subtype.</summary>
      Normal
    | /// <summary>This item has a named subtype.</summary>
      Named of string

/// <summary>
///     An extended type record for primitive types.
/// </summary>
type PrimTypeRec =
    { /// <summary>The subtype of this primitive type.</summary>
      PrimSubtype : Subtype }

/// <summary>
///     An extended type record for array types.
/// </summary>
type ArrayTypeRec =
    { /// <summary>The element type of the array.</summary>
      ElementType : Type
      /// <summary>The length of the array.</summary>
      Length : int option }

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
and Typed<'Int, 'Bool, 'Array> =
    /// <summary>An item of integral type.</summary>
    | Int of typerec : PrimTypeRec * value : 'Int
    /// <summary>
    ///    An item of Boolean type.
    /// </summary>
    | Bool of typerec : PrimTypeRec * value: 'Bool
    /// <summary>
    ///    An item of array type, annotated by the type of the array element
    ///    and an optional length.
    /// </summary>
    | Array of typerec : ArrayTypeRec * value : 'Array
    override this.ToString() =
        match this with
        | Int (_, x) -> sprintf "I(%A)" x
        | Bool (_, x) -> sprintf "B(%A)" x
        | Array ({ ElementType = eltype; Length = length}, x) -> sprintf "A<%A, %A>(%A)" eltype length x

/// <summary>
///     A typed item where every type leads to the same meta-type.
/// </summary>
/// <typeparam name="T">
///     The meta-type to use for all <c>Typed</c> parameters.
/// </typeparam>
and CTyped<'T> = Typed<'T, 'T, 'T>

/// <summary>
///     A standalone type annotation.
/// </summary>
and Type = CTyped<unit>

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
        | Bool (t, _) -> Bool (t, ())
        | Int (t, _) -> Int (t, ())
        | Array (t, _) -> Array (t, ())

    /// <summary>
    ///     Maps over the contents of a <see cref="CTyped"/>.
    /// </summary>
    /// <param name="f">The function to map.</param>
    /// <param name="ctyped">The <see cref="CTyped"/> to map.</param>
    /// <returns>
    ///     The result of applying <paramref name="f"/> on <paramref name="CTyped"/>.
    /// </returns>
    /// <typeparam name="Src">
    ///     The meta-type of items entering the map.
    /// </typeparam>
    /// <typeparam name="Dst">
    ///     The meta-type of items leaving the map.
    /// </typeparam>
    let mapCTyped (f : 'Src -> 'Dst) (ctyped : CTyped<'Src>) : CTyped<'Dst> =
        match ctyped with
        | Int (t, i) -> Int (t, f i)
        | Bool (t, b) -> Bool (t, f b)
        | Array (t, a) -> Array (t, f a)

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
        mapCTyped (fun _ -> item) ty

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
        | Int (_, a) | Bool (_, a) | Array (_, a) -> a

    /// <summary>
    ///     Active pattern splitting a CTyped item into its item and type.
    /// </summary>
    let (|WithType|) x = (valueOf x, typeOf x)

    /// <summary>
    ///     Active pattern extracting the root type of a typed item.
    /// </summary>
    let (|AnInt|ABool|AnArray|) (typed : Typed<'I, 'B, 'A>) =
        match typed with
        | Int _ -> AnInt
        | Bool _ -> ABool
        | Array ({ ElementType = eltype; Length = length }, _) -> AnArray (eltype, length)

    /// <summary>
    ///     Active pattern extracting the full root type of a typed item.
    /// </summary>
    let (|AnIntR|ABoolR|AnArrayR|) (typed : Typed<'I, 'B, 'A>) =
        match typed with
        | Int (t, _) -> AnIntR t
        | Bool (t, _) -> ABoolR t
        | Array (t, _) -> AnArrayR t

/// <summary>
///     Tries to unify a list of primitive type records.
/// </summary>
/// <param name="xs">The possibly empty list of type records to check.</param>
/// <returns>
///     The unified record, if unification is possible; None otherwise.
/// </returns>
let rec unifyPrimTypeRecs (xs : PrimTypeRec list) : PrimTypeRec option =
    match xs with
    | [] -> Some { PrimSubtype = Indef }
    | x::xs ->
        (* TODO(CaptainHayashi): this is way too strong and order-dependent.
           It's also somewhat broken, but in mostly inconsequential ways. *)
        let foldRecs recSoFar nextRec =
            match recSoFar with
            | None -> None
            | Some rs ->
                match rs.PrimSubtype, nextRec.PrimSubtype with
                | _, Indef -> Some rs
                | Indef, _ -> Some nextRec
                | Normal, Normal -> Some rs
                | Named x, Named y when x = y -> Some rs
                | _ -> None
        List.fold foldRecs (Some x) xs

/// <summary>
///     Checks whether two primitive type records are compatible.
/// </summary>
/// <param name="x">The first type record to check.</param>
/// <param name="y">The second type record to check.</param>
/// <returns>
///     True if <paramref name="x"/> can be made compatible with
///     <paramref name="y"/>, or vice versa; false otherwise.
/// </returns>
let rec primTypeRecsCompatible (x : PrimTypeRec) (y : PrimTypeRec) : bool =
    match unifyPrimTypeRecs [x; y] with
    | Some _ -> true
    | None -> false

/// <summary>
///     Tries to unify a list of primitive type records.
/// </summary>
/// <param name="xs">The possibly empty list of type records to check.</param>
/// <returns>
///     The unified record, if unification is possible; None otherwise.
/// </returns>
let rec unifyArrayTypeRecs (xs : ArrayTypeRec list) : ArrayTypeRec option =
    // TODO(CaptainHayashi): add to this when PrimTypeRec expands.
    match xs with
    | [] -> None
    | x::xs ->
        (* TODO(CaptainHayashi): this is way too strong and order-dependent.
           It's also somewhat broken, but in mostly inconsequential ways. *)
        let foldRecs recSoFar nextRec =
            match recSoFar with
            | None -> None
            | Some rs ->
                // TODO(CaptainHayashi): unify element types.
                match unifyTwoTypes rs.ElementType nextRec.ElementType with
                | Some et ->
                    (* Currently, favour the type with the most defined length.
                       This should really pull the unified type from above
                       instead of taking one or the other. *)
                    match (rs.Length, nextRec.Length) with
                    | Some l, None | None, Some l ->
                        Some { ElementType = et; Length = Some l }
                    | None, None ->
                        Some { ElementType = et; Length = None }
                    | Some x, Some y when x = y ->
                        Some { ElementType = et; Length = Some x }
                    | _ -> None
                | None -> None
        List.fold foldRecs (Some x) xs

/// <summary>
///     Checks whether two array type records are compatible.
/// </summary>
/// <param name="x">The first type record to check.</param>
/// <param name="y">The second type record to check.</param>
/// <returns>
///     True if <paramref name="x"/> can be made compatible with
///     <paramref name="y"/>, or vice versa; false otherwise.
/// </returns>
and arrayTypeRecsCompatible (x : ArrayTypeRec) (y : ArrayTypeRec) : bool =
    match unifyArrayTypeRecs [x; y] with
    | Some _ -> true
    | None -> false

/// <summary>
///     Tries to unify two types.
/// </summary>
/// <param name="x">The first type to unify.</param>
/// <param name="y">The second type to unify.</param>
/// <returns>
///     The unified record, if unification is possible; None otherwise.
/// </returns>
and unifyTwoTypes (x : Type) (y : Type) : Type option =
    (* Types are can be unified when their base types are equal and their
       extended type records are unifiable. *)
    match (x, y) with
    | (AnIntR xr, AnIntR yr) ->
        Option.map (fun tr -> Int (tr, ())) (unifyPrimTypeRecs [xr; yr])
    | (ABoolR xr, ABoolR yr) ->
        Option.map (fun tr -> Bool (tr, ())) (unifyPrimTypeRecs [xr; yr])
    | (AnArrayR xr, AnArrayR yr) ->
        Option.map (fun tr -> Array (tr, ())) (unifyArrayTypeRecs [xr; yr])
    | _ -> None

/// <summary>
///     Checks whether two types are compatible.
/// </summary>
/// <param name="x">The first type to check.</param>
/// <param name="y">The second type to check.</param>
/// <returns>
///     True if <paramref name="x"/> can be made compatible with
///     <paramref name="y"/>, or vice versa; false otherwise.
/// </returns>
and typesCompatible (x : Type) (y : Type) : bool =
    match unifyTwoTypes x y with
    | Some _ -> true
    | None -> false


/// <summary>
///     Pretty printers for the type system.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// <summary>
    ///     Pretty-prints a type.
    /// </summary>
    let rec printType (ty : Type) : Doc =
        match ty with
        | AnIntR { PrimSubtype = Indef } -> String "int?"
        | AnIntR { PrimSubtype = Normal } -> String "int"
        | AnIntR { PrimSubtype = Named x } -> String x
        | ABoolR { PrimSubtype = Indef } -> String "bool?"
        | ABoolR { PrimSubtype = Normal } -> String "bool"
        | ABoolR { PrimSubtype = Named x } -> String x
        | AnArrayR { ElementType = eltype; Length = len } ->
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
            | Int (_, a) -> pInt a
            | Bool (_, a) -> pBool a
            | Array ({ ElementType = eltype; Length = length }, a) -> pArray eltype length a

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
