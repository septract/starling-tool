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
///     A standalone type annotation.
/// </summary>
type Type = CTyped<unit>

/// <summary>
///     A table of mapping functions from one <c>Typed</c> type to
///     another.
///
///     <para>
///          <c>Mapper</c>s can also carry around a context, for use in
///          situations such as changing the mapping depending on
///          whether we are in a positive or negative position in a
///          Boolean.
///     </para>
/// </summary>
/// <typeparam name="context">
///     The type of the context.
/// </typeparam>
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
type Mapper<'context, 'srcInt, 'srcBool, 'dstInt, 'dstBool> =
    private
        { /// <summary>
          ///     Mapping function for integers.
          /// </summary>
          I: 'context -> 'srcInt -> ('context * 'dstInt)
          /// <summary>
          ///     Mapping function for Booleans.
          /// </summary>
          B: 'context -> 'srcBool -> ('context * 'dstBool) }

/// <summary>
///     A table of mapping functions from one <c>CTyped</c> type to another.
/// </summary>
/// <typeparam name="context">
///     The type of the context.
/// </typeparam>
/// <typeparam name="src">
///     The type of values entering the map.
/// </typeparam>
/// <typeparam name="dst">
///     The type of typed values leaving the map.
/// </typeparam>
[<NoComparison>]
[<NoEquality>]
type CMapper<'context, 'src, 'dst> = Mapper<'context, 'src, 'src, 'dst, 'dst>


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
///     Functions and types for mapping typed values.
/// </summary>
module Mapper =
    /// <summary>
    ///     Runs a <c>Mapper</c> on an integral value, using context.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run.
    /// </param>
    /// <param name="context">
    ///     The context to use.
    /// </param>
    /// <typeparam name="context">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
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
    let mapIntCtx
      (tm : Mapper<'context, 'srcInt, _, 'dstInt, _>)
      : 'context -> 'srcInt -> ('context * 'dstInt) =
        tm.I

    /// <summary>
    ///     Runs a <c>Mapper</c> on a Boolean value, with context.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run, using context.
    /// </param>
    /// <param name="context">
    ///     The context to use.
    /// </param>
    /// <typeparam name="context">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
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
    let mapBoolCtx
      (tm : Mapper<'context, _, 'srcBool, _, 'dstBool>)
      : 'context -> 'srcBool -> ('context * 'dstBool) =
        tm.B

    /// <summary>
    ///     Runs a possibly failing <c>Mapper</c> on a <c>Typed</c>
    ///     value, with context.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run, with context.
    /// </param>
    /// <param name="context">
    ///     The context to use.
    /// </param>
    /// <typeparam name="context">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    ///     This excludes the Chessie <c>Result</c>.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    ///     This excludes the Chessie <c>Result</c>.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of errors occurring in the map.
    /// </typeparam>
    /// <returns>
    ///     A function mapping over a <c>Typed</c> value with
    ///     <paramref name="tm"/>, returning a <c>Result</c> over
    ///     <c>'err</c>.
    /// </returns>
    let tryMapCtx
      (tm :
           Mapper<
               'context,
               'srcInt, 'srcBool,
               Result<'dstInt, 'err>, Result<'dstBool, 'err>> )
      (context : 'context)
      : (Typed<'srcInt, 'srcBool> ->
             ('context * Result<Typed<'dstInt, 'dstBool>, 'err>)) =
        function
        | Typed.Int i -> i |> mapIntCtx tm context |> pairMap id (lift Typed.Int)
        | Typed.Bool i -> i |> mapBoolCtx tm context |> pairMap id (lift Typed.Bool)

    /// <summary>
    ///     Runs a <c>Mapper</c> on a <c>Typed</c> value, with context.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run, with context.
    /// </param>
    /// <param name="context">
    ///     The context to use.
    /// </param>
    /// <typeparam name="context">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
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
    let mapCtx
      (tm : Mapper<'context, 'srcInt, 'srcBool, 'dstInt, 'dstBool>)
      (context : 'context)
      : (Typed<'srcInt, 'srcBool> -> ('context * Typed<'dstInt, 'dstBool>)) =
        function
        | Typed.Int i -> i |> mapIntCtx tm context |> pairMap id Typed.Int
        | Typed.Bool i -> i |> mapBoolCtx tm context |> pairMap id Typed.Bool

    /// <summary>
    ///     Runs a <c>Mapper</c> on an integral value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run.  The <c>Mapper</c> cannot have a
    ///     context.
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
      (tm : Mapper<unit, 'srcInt, _, 'dstInt, _>)
      : 'srcInt -> 'dstInt =
        tm.I () >> snd

    /// <summary>
    ///     Runs a <c>Mapper</c> on a Boolean value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run.  The <c>Mapper</c> cannot have a
    ///     context.
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
      (tm : Mapper<unit, _, 'srcBool, _, 'dstBool>)
      : 'srcBool -> 'dstBool =
        tm.B () >> snd

    /// <summary>
    ///     Runs a possibly failing <c>Mapper</c> on a <c>Typed</c> value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run.  The mapper must have no context.
    /// </param>
    /// <typeparam name="srcInt">
    ///     The type of <c>Int</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="srcBool">
    ///     The type of <c>Bool</c>-typed values entering the map.
    /// </typeparam>
    /// <typeparam name="dstInt">
    ///     The type of <c>Int</c>-typed values leaving the map.
    ///     This excludes the Chessie <c>Result</c>.
    /// </typeparam>
    /// <typeparam name="dstBool">
    ///     The type of <c>Bool</c>-typed values leaving the map.
    ///     This excludes the Chessie <c>Result</c>.
    /// </typeparam>
    /// <typeparam name="err">
    ///     The type of errors occurring in the map.
    /// </typeparam>
    /// <returns>
    ///     A function mapping over a <c>Typed</c> value with
    ///     <paramref name="tm"/>, returning a <c>Result</c> over
    ///     <c>'err</c>.
    /// </returns>
    let tryMap
      (tm :
           Mapper<
               unit,
               'srcInt, 'srcBool,
               Result<'dstInt, 'err>, Result<'dstBool, 'err>> )
      : (Typed<'srcInt, 'srcBool> ->
             Result<Typed<'dstInt, 'dstBool>, 'err>) =
        function
        | Typed.Int i -> i |> mapInt tm |> lift Typed.Int
        | Typed.Bool i -> i |> mapBool tm |> lift Typed.Bool

    /// <summary>
    ///     Runs a <c>Mapper</c> on a <c>Typed</c> value.
    /// </summary>
    /// <param name="tm">
    ///     The <c>Mapper</c> to run.  The <c>Mapper</c> must have no
    ///     context.
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
      (tm : Mapper<unit, 'srcInt, 'srcBool, 'dstInt, 'dstBool>)
      : (Typed<'srcInt, 'srcBool> -> Typed<'dstInt, 'dstBool>) =
        function
        | Typed.Int i -> i |> mapInt tm |> Typed.Int
        | Typed.Bool i -> i |> mapBool tm |> Typed.Bool

    /// <summary>
    ///     Constructs a <c>Mapper</c> that uses context.
    /// </summary>
    /// <param name="iFun">
    ///     The function to apply on integral values.
    /// </param>
    /// <param name="bFun">
    ///     The function to apply on Boolean values.
    /// </param>
    /// <typeparam name="context">
    ///     The type of the context.  Context may be changed.
    /// </typeparam>
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
    ///     A <c>Mapper</c> using <paramref name="iFun"/> and
    ///     <paramref name="bFun"/>, and taking and returning context.
    /// </returns>
    let makeCtx
      (iFun : 'context -> 'srcInt -> ('context * 'dstInt))
      (bFun : 'context -> 'srcBool -> ('context * 'dstBool))
      : Mapper<'context, 'srcInt, 'srcBool, 'dstInt, 'dstBool> =
        { I = iFun
          B = bFun }

    /// <summary>
    ///     Constructs a <c>Mapper</c>.
    /// </summary>
    /// <param name="iFun">
    ///     The function to apply on integral values.
    /// </param>
    /// <param name="bFun">
    ///     The function to apply on Boolean values.
    /// </param>
    /// <typeparam name="context">
    ///     The type of the context.  Context is passed through unused.
    /// </typeparam>
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
    ///     A <c>Mapper</c> using <paramref name="iFun"/> and
    ///     <paramref name="bFun"/>.  The mapper passes through context
    ///     unused.
    /// </returns>
    let make
      (iFun : 'srcInt -> 'dstInt)
      (bFun : 'srcBool -> 'dstBool)
      : Mapper<'context, 'srcInt, 'srcBool, 'dstInt, 'dstBool> =
        makeCtx (fun c i -> (c, iFun i)) (fun c b -> (c, bFun b))

    /// <summary>
    ///     Constructs a <c>Mapper</c> over <c>CTyped</c> that uses context.
    /// </summary>
    /// <param name="f">
    ///     The function to apply on all values.
    /// </param>
    /// <typeparam name="context">
    ///     The type of the context.  Context may be changed.
    /// </typeparam>
    /// <typeparam name="src">
    ///     The type of values entering the map.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The type of values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A <c>CMapper</c> using <paramref name="f"/>, passing
    ///     through the context unused.
    /// </returns>
    let cmakeCtx (f : 'context -> 'src -> ('context * 'dst))
      : CMapper<'context, 'src, 'dst> =
        makeCtx f f

    /// <summary>
    ///     Constructs a <c>Mapper</c> over <c>CTyped</c>.
    /// </summary>
    /// <param name="f">
    ///     The function to apply on all values.
    /// </param>
    /// <typeparam name="context">
    ///     The type of the context.  Context is passed through unused.
    /// </typeparam>
    /// <typeparam name="src">
    ///     The type of values entering the map.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The type of values leaving the map.
    /// </typeparam>
    /// <returns>
    ///     A <c>CMapper</c> using <paramref name="f"/>, passing
    ///     through the context unused.
    /// </returns>
    let cmake (f : 'src -> 'dst) : CMapper<'context, 'src, 'dst> =
        make f f

    /// <summary>
    ///     Composes two <c>Mapper</c>s.
    /// </summary>
    /// <param name="f">
    ///     The <c>Mapper</c> to apply first.
    /// </param>
    /// <param name="g">
    ///     The <c>Mapper</c> to apply second.
    /// </param>
    /// <typeparam name="context">
    ///     The type of the context passed through.
    /// </typeparam>
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
    ///     A <c>Mapper</c> composing <paramref name="f"/> and
    ///     <paramref name="g"/> left-to-right.
    /// </returns>
    let compose
      (f : Mapper<'context, 'srcInt, 'srcBool, 'fInt, 'fBool>)
      (g : Mapper<'context, 'fInt, 'fBool, 'dstInt, 'dstBool>)
      : Mapper<'context, 'srcInt, 'srcBool, 'dstInt, 'dstBool> =
        { I = fun c i -> (c, i) ||> f.I ||> g.I
          B = fun c b -> (c, b) ||> f.B ||> g.B }


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
    let typeOf (typed : Typed<_, _> ) : Type =
        Mapper.map
            (Mapper.make
                (fun _ -> ())
                (fun _ -> ()))
            typed

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
        Mapper.map (Mapper.cmake (fun _ -> item)) ty

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
///     Pretty printers for the type system.
/// </summary>
module Pretty =
    open Starling.Core.Pretty

    /// <summary>
    ///     Pretty-prints a type.
    /// </summary>
    let printType : Type -> Command =
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
    ///     A printer <c>Command</c> printing <paramref name="ctyped"/>.
    /// </returns>
    let printCTyped
      (pItem : 'item -> Command)
      (ctyped : CTyped<'item>)
      : Command =
        hsep
            [ printType (typeOf ctyped)
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
    ///     <c>Command</c>s.
    /// </returns>
    let printTyped
      (pInt : 'int -> Command)
      (pBool : 'bool -> Command)
      : Typed<'int, 'bool> -> Command =
        Mapper.map (Mapper.make pInt pBool) >> printCTyped id
