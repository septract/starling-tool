/// <summary>
///     Collections used in Starling.
/// </summary>
module Starling.Collections

open Chessie.ErrorHandling
open Starling.Utils

/// <summary>
///     A function-like construct.
/// </summary>
/// <remarks>
///     <para>
///         A Func is a combination of a string name and list of parameters.
///         It generically represents any pattern <c>Name(p1, p2, .., pn)</c>
///         in Starling.
///     </para>
///     <para>
///         Examples of Func uses in Starling include function signatures and
///         calls, components of <see cref="T:Starling.Model">views</see>, and
///         Horn clause predicates.
///     </para>
/// </remarks>
/// <typeparam name="param">The type of parameters in the Func.</typeparam>
type Func<'param> =
    { /// The name of a Func.
      Name : string
      /// The parameters of a Func.
      Params : 'param list }
    override this.ToString () = sprintf "Func: %s(%A)" this.Name this.Params

/// <summary>
///     Creates a new <c>Func</c>.
/// </summary>
/// <parameter name="name">
///     The name of the <c>Func</c>.
/// </parameter>
/// <parameter name="pars">
///     The parameters of the <c>Func</c>, as a sequence.
/// </parameter>
/// <returns>
///     A new <c>Func</c> with the given name and parameters.
/// </returns>
let func (name : string)
         (pars : 'param seq)
         : Func<'param> =
    { Name = name; Params = List.ofSeq pars }

module Func =
    module Pretty =
        open Starling.Core

        /// Pretty-prints Funcs using pxs to print parameters.
        let printFunc pxs { Name = f; Params = xs } = Pretty.func f (Seq.map pxs xs)

/// <summary>
///     A multiset, or ordered list.
/// </summary>
/// <typeparam name="item">
///     The type of items in the Multiset.
/// </typeparam>
type Multiset<'item> when 'item: comparison =
    | MSet of Map<'item, int>
    override this.ToString() = sprintf "%A" this


/// <summary>
///     Operations on multisets.
/// </summary>
/// <seealso cref="T:Starling.Collections.Multiset`1" />
module Multiset =
    (*
     * Construction
     *)

    /// <summary>
    ///     The empty multiset.
    /// </summary>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    let empty : Multiset<'item> = MSet (Map.empty)

    /// <summary>
    ///     Adds an element n times to a multiset
    /// </summary>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    let addn (MSet ms : Multiset<'item>)
             (k : 'item)
             (m : int)
             : Multiset<'item> =
        let n = ms.TryFind k |> Option.fold (fun _ y -> y) 0
        MSet (ms.Add (k, n+m))

    /// <summary>
    ///     Adds an element to a multiset
    /// </summary>
    let add (ms : Multiset<'item>) (k : 'item) : Multiset<'item> = addn ms k 1

    /// <summary>
    ///     Creates a multiset with the given flat sequence as its contents.
    /// </summary>
    /// <param name="xs">
    ///     The flat sequence to use to create the multiset.
    /// </param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     A multiset containing the given items.
    /// </returns>
    let ofFlatSeq (xs : 'item seq) : Multiset<'item> =
        Seq.fold add empty xs

    /// <summary>
    ///     Creates a multiset with the given flat list as its contents.
    /// </summary>
    /// <param name="xs">
    ///     The flat list to use to create the multiset.
    /// </param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     A multiset containing the given items.
    /// </returns>
    let ofFlatList (xs : 'item list) : Multiset<'item> =
        xs |> ofFlatSeq

    /// <summary>
    ///     Creates a multiset with one item.
    /// </summary>
    /// <param name="x">
    ///     The item to place in the multiset.
    /// </param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     A singleton multiset.
    /// </returns>
    let singleton (x : 'item) : Multiset<'item> = add empty x


    (*
     * Destruction
     *)

    /// <summary>
    ///     Converts a multiset to a sorted, flattened sequence.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     The sorted, flattened sequence.
    /// </returns>
    let toFlatSeq (MSet ms : Multiset<'item>) : 'item seq =
        // TODO(CaptainHayashi): this will be removed when itviews land.
        ms
        |> Map.toSeq
        |> Seq.map (fun (k, amount) -> Seq.replicate amount k)
        |> Seq.concat

    /// <summary>
    ///     Converts a multiset to a sorted, flattened list.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     The sorted, flattened list.
    /// </returns>
    let toFlatList (ms : Multiset<'item>) : 'item list =
        // TODO(CaptainHayashi): this will be removed when itviews land.
        ms
        |> toFlatSeq
        |> List.ofSeq

    /// <summary>
    ///     Converts a multiset to a set, removing duplicates.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     The set of items in the multiset.
    /// </returns>
    let toSet (MSet ms : Multiset<'item>) : Set<'item> =
        // TODO(CaptainHayashi): this _may_ be removed when itviews land,
        // as it will be impossible to decide whether, if something is in
        // the list an unknown amount of times, that amount > 0.
        Map.fold (fun set k _ -> Set.add k set) Set.empty ms

    (*
     * Operations
     *)

    /// <summary>
    ///     Takes the length of a multiset.
    /// </summary>
    /// <param name="mset">
    ///     The multiset to measure.
    /// </param>
    /// <returns>
    ///     The number of elements in <paramref name="_arg1" />.
    /// </returns>
    let length (MSet mset : Multiset<_>) : int =
        // TODO(CaptainHayashi): this will be removed when itviews land.
        mset |> Map.fold (fun count _ n -> count + n) 0

    /// <summary>
    ///     Appends two multisets.
    /// </summary>
    /// <remarks>
    ///     Since multisets are ordered, the resulting multiset may not
    ///     necessarily be <c>xs</c> followed by <c>ys</c>.
    /// </remarks>
    /// <param name="xs">The first multiset to append.</param>
    /// <param name="ys">The second multiset to append.</param>
    /// <typeparam name="item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     The result of appending <c>xs</c> to <c>ys</c>.
    /// </returns>
    let append (xs : Multiset<'item>)
               (MSet ymap : Multiset<'item>)
               : Multiset<'item> =
        Map.fold addn xs ymap

    /// <summary>
    ///     Folds <c>f</c> over the unique items of a multiset in some
    ///     arbitrary order.
    /// </summary>
    /// <param name="f">
    ///     The function to fold over the multiset.  This takes the current
    ///     state, the item, and the number of times that item
    ///     appears in the multiset.  It should return the new state.
    /// </param>
    /// <param name="init">
    ///     The initial value of the state.
    /// </param>
    /// <typeparam name="State">
    ///     The type of the accumulator.
    /// </typeparam>
    /// <typeparam name="Item">
    ///     The type of items in the multiset.
    /// </typeparam>
    /// <returns>
    ///     The final value of the state.
    /// </returns>
    let fold (f : 'State -> 'Item -> int -> 'State)
      (init : 'State)
      (MSet ms : Multiset<'Item>)
      : 'State =
        ms
        |> Map.toSeq
        |> Seq.fold (fun state (item, num) -> f state item num) init

    /// <summary>
    ///     Maps <c>f</c> over the unique items of a multiset, passing
    ///     an accumulator in some arbitrary order.
    /// </summary>
    /// <param name="f">
    ///     The function to map over the multiset.  This takes the
    ///     accumulator, the item, and the number of times that item
    ///     appears in the multiset.  It should return the new item.  It
    ///     is assumed the number of appearances does not change.
    /// </param>
    /// <param name="init">
    ///     The initial value of the accumulator.
    /// </param>
    /// <typeparam name="acc">
    ///     The type of the accumulator.
    /// </typeparam>
    /// <typeparam name="src">
    ///     The type of variables in the list to map.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The type of variables in the list after mapping.
    /// </typeparam>
    /// <returns>
    ///     The pair of the final value of the accumulator, and the
    ///     result of mapping <c>f</c> over the multiset.
    /// </returns>
    /// <remarks>
    ///     Since multisets are ordered, mapping can change the position of
    ///     items.
    /// </remarks>
    let mapAccum
      (f : 'acc -> 'src -> int -> ('acc * 'dst))
      (init : 'acc)
      (MSet ms : Multiset<'src>)
      : ('acc * Multiset<'dst>) =
        // TODO(CaptainHayashi): convert map to a similar abstraction.
        ms
        |> Map.toList
        |> mapAccumL
               (fun acc (src, num) ->
                   let acc', dst = f acc src num
                   (acc', (dst, num)))
               init
        |> pairMap id (Map.ofList >> MSet)

    /// <summary>
    ///     Maps <c>f</c> over a multiset.
    /// </summary>
    /// <remarks>
    ///     Since multisets are ordered, mapping can change the position of
    ///     items.
    /// </remarks>
    /// <param name="f">The function to map over the multiset.</param>
    /// <typeparam name="src">
    ///     The type of variables in the list to map.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The type of variables in the list after mapping.
    /// </typeparam>
    /// <returns>
    ///     The result of mapping <c>f</c> over the multiset.
    /// </returns>
    let map (f : 'src -> 'dst)
            (MSet xs : Multiset<'src>)
            : Multiset<'dst> =
        let rec repeat_add map k n =
            match n with
            | 0 -> map
            | n -> repeat_add (add map (f k)) k (n-1)
        //Note that this is used with side-effecting f, so must be called n times for each addition.
        Map.fold repeat_add empty xs

    /// <summary>
    ///     Collapses a multiset of results to a result on a multiset.
    /// </summary>
    /// <param name="_arg1">
    ///     The multiset to collect.
    /// </param>
    /// <typeparam name="item">
    ///     Type of items in the multiset.
    /// </typeparam>
    /// <typeparam name="err">
    ///     Type of errors in the result.
    /// </typeparam>
    /// <returns>
    ///     A result, containing the collected form of
    ///     <paramref name="_arg1" />.
    /// </returns>
    let collect
      (MSet ms : Multiset<Result<'item, 'err>>)
      : Result<Multiset<'item>, 'err> =
        // TODO(CaptainHayashi): unify with map?
        let rec itr tos fros warns : Result<Multiset<'item>, 'err> =
            match tos with
            | [] -> ok (MSet (Map.ofList fros))
            | ((Warn (x, ws), n)::xs) -> itr xs ((x, n)::fros) (ws@warns)
            | ((Pass x, n)::xs) -> itr xs ((x, n)::fros) warns
            | ((Fail e, n)::xs) -> Bad e
        itr (Map.toList ms) [] []

    /// <summary>
    ///     Pulls an arbitrary item out of the multiset.
    /// </summary>
    /// <param name="ms">
    ///     The multiset.
    /// </param>
    /// <typeparam name="Item">
    ///     The type of items in the multiset's lists.
    /// </typeparam>
    /// <returns>
    ///     An option: <c>None</c> if the multiset is empty; else
    ///     <c>Some (i, m, n)</c> where <c>i</c> is an item in the multiset,
    ///     <c>m</c> is the multiset less <c>i</c>, and
    ///     <c>n</c> is the number of times it occurs.
    /// </returns>
    let pop (MSet ms : Multiset<'Item>)
      : ('Item * Multiset<'Item> * int) option =
        // TODO(CaptainHayashi): tests.
        match (Map.toList ms) with
        | [] -> None
        | (i, n)::xs -> Some (i, MSet (Map.ofList xs), n)

    module Pretty =
        open Starling.Core.Pretty
        /// Pretty-prints a multiset given a printer for its contents.
        let printMultiset pItem =
            toFlatList
            >> List.map pItem
            >> semiSep
