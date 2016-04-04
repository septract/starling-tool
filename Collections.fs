/// Collections used in Starling.
module Starling.Collections

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
let func name pars = { Name = name; Params = List.ofSeq pars }

/// <summary>
///     A multiset, or ordered list.
/// </summary>
/// <typeparam name="item">
///     The type of items in the Multiset.
/// </typeparam>
type Multiset<'item> when 'item: comparison =
    | MSet of Map<'item, int>

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
    let empty = MSet (Map.empty)

    /// <summary>
    ///     Creates a multiset with the given flat sequence as its contents.
    /// </summary>
    /// <param name="xs">
    ///     The flat sequence to use to create the multiset.
    /// </param>
    /// <returns>
    ///     A multiset containing the given items.
    /// </returns>
    let ofSeq xs =
        xs
        // First, collate into (k, [k, k, ...]) form...
        |> Seq.groupBy id
        // then, turn into (k, occurences of k).
        |> Seq.map (pairMap id Seq.length)
        |> Map.ofSeq
        |> MSet

    /// <summary>
    ///     Creates a multiset with the given flat list as its contents.
    /// </summary>
    /// <param name="xs">
    ///     The flat list to use to create the multiset.
    /// </param>
    /// <returns>
    ///     A multiset containing the given items.
    /// </returns>
    let ofList xs =
        xs |> List.toSeq |> ofSeq

    /// <summary>
    ///     Creates a multiset with one item.
    /// </summary>
    /// <param name="x">
    ///     The item to place in the multiset.
    /// </param>
    /// <returns>
    ///     A singleton multiset.
    /// </returns>
    let singleton x = ofList [ x ]


    (*
     * Destruction
     *)

    /// <summary>
    ///     Converts a multiset to a sorted, flattened sequence.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <returns>
    ///     The sorted, flattened sequence.
    /// </returns>
    let toSeq (MSet ms) =
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
    /// <returns>
    ///     The sorted, flattened list.
    /// </returns>
    let toList ms =
        ms
        |> toSeq
        |> List.ofSeq

    /// <summary>
    ///     Converts a multiset to a set, removing duplicates.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <returns>
    ///     The set of items in the multiset.
    /// </returns>
    let toSet ms =
        ms
        |> toSeq
        |> Set.ofSeq

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
    let length mset =
        mset |> toSeq |> Seq.length

    /// <summary>
    ///     Appends two multisets.
    /// </summary>
    /// <remarks>
    ///     Since multisets are ordered, the resulting multiset may not
    ///     necessarily be <c>xs</c> followed by <c>ys</c>.
    /// </remarks>
    ///
    /// <param name="xs">The first multiset to append.</param>
    /// <param name="ys">The second multiset to append.</param>
    ///
    /// <returns>
    ///     The result of appending <c>xs</c> to <c>ys</c>.
    /// </returns>
    let append xs ys =
        // TODO(CaptainHayashi): a more efficient algorithm for this.
        Seq.append (toSeq xs) (toSeq ys) |> ofSeq

    /// <summary>
    ///     Maps <c>f</c> over a multiset.
    /// </summary>
    /// <remarks>
    ///     Since multisets are ordered, mapping can change the position of
    ///     items.
    /// </remarks>
    ///
    /// <param name="f">The function to map over the multiset.</param>
    ///
    /// <returns>
    ///     The result of mapping <c>f</c> over the multiset.
    /// </returns>
    let map f =
        // TODO(CaptainHayashi): quite inefficient, but not sure how
        // else to do this correctly.
        toList
        >> List.map f
        >> ofList

    /// Produces the power-multiset of a multiset, as a set of multisets.
    let power msm =
        (* Solve the problem using Boolean arithmetic on the index of the
         * powerset item.
         *)
        let ms = toList msm
        seq {
            for i in 0..(1 <<< List.length ms) - 1 do
                yield (seq { 0..(List.length ms) - 1 } |> Seq.choose (fun j -> 
                                                              let cnd : int = i &&& (1 <<< j)
                                                              if cnd <> 0 then Some ms.[j]
                                                              else None))
                      |> ofSeq
        }
        |> Set.ofSeq

/// <summary>
///     Tests for collections.
/// </summary>
module Tests =
    open NUnit.Framework

    let tcd : obj[] -> TestCaseData = TestCaseData

    /// <summary>
    ///    NUnit tests for collections.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for <c>Multiset.ofList</c>.
        /// </summary>
        static member ListMultisets =
            [ TestCaseData([10; 23; 1; 85; 23; 1] : int list)
                 .Returns(([ (1, 2)
                             (10, 1)
                             (23, 2)
                             (85, 1) ]
                          |> Map.ofList |> MSet) : Multiset<int>)
                 .SetName("A populated list produces the expected multiset")
              TestCaseData([] : int list)
                 .Returns(MSet (Map.empty) : Multiset<int>)
                 .SetName("An empty list produces the empty multiset") ]

        /// <summary>
        ///     Tests <c>Multiset.ofList</c>.
        /// </summary>
        [<TestCaseSource("ListMultisets")>]
        member x.``Multiset.ofList creates correct multisets`` l =
            (Multiset.ofList l) : Multiset<int>


        /// <summary>
        ///     Test cases for <c>Multiset.toList</c>.
        /// </summary>
        static member MultisetLists =
            [ TestCaseData(MSet (Map.ofList [ (1, 2)
                                              (10, 1)
                                              (23, 2)
                                              (85, 1) ] ) : Multiset<int>)
                 .Returns([1; 1; 10; 23; 23; 85] : int list)
                 .SetName("A populated multiset produces the expected list")
              TestCaseData(MSet (Map.empty) : Multiset<int>)
                 .Returns([] : int list)
                 .SetName("An empty multiset produces the empty list") ]

        /// <summary>
        ///     Tests <c>Multiset.ofList</c>.
        /// </summary>
        [<TestCaseSource("MultisetLists")>]
        member x.``Multiset.toList creates correct lists`` ms =
            (Multiset.toList ms) : int list


        /// <summary>
        ///     Test cases for <c>Multiset.append</c>.
        /// </summary>
        static member MultisetAppends =
            [ (tcd [| (Multiset.empty : Multiset<int>)
                      (Multiset.empty : Multiset<int>) |])
                 .Returns(MSet (Map.empty) : Multiset<int>)
                 .SetName("Appending two empty msets yields the empty mset")
              (tcd [| (Multiset.ofList [1; 2; 3] : Multiset<int>)
                      (Multiset.empty : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (1, 1) ; (2, 1) ; (3, 1) ] )
                               : Multiset<int>)
                 .SetName("Appending x and an empty mset yields x")
              (tcd [| (Multiset.empty : Multiset<int>)
                      (Multiset.ofList [4; 5] : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (4, 1) ; (5, 1) ] )
                               : Multiset<int>)
                 .SetName("Appending an empty mset and x yields x")
              (tcd [| (Multiset.ofList [1; 3; 5] : Multiset<int>)
                      (Multiset.ofList [2; 4; 6] : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (1, 1)
                                             (2, 1)
                                             (3, 1)
                                             (4, 1)
                                             (5, 1)
                                             (6, 1) ]) : Multiset<int>)
                 .SetName("Appending two msets works as expected") ]

        /// <summary>
        ///     Tests <c>Multiset.append</c>.
        /// </summary>
        [<TestCaseSource("MultisetAppends")>]
        member x.``Multiset.append appends multisets correctly`` a b =
            (Multiset.append a b) : Multiset<int>


        /// <summary>
        ///     Test cases for <c>Multiset.length</c>.
        /// </summary>
        static member MultisetLength =
            [ (tcd [| (Multiset.empty : Multiset<int>) |])
                 .Returns(0)
                 .SetName("The empty mset contains 0 items")
              (tcd [| (Multiset.ofList [ 1 ; 2 ; 3 ] : Multiset<int>) |])
                 .Returns(3)
                 .SetName("A disjoint mset's length is the number of items")
              (tcd [| (Multiset.ofList [ 1 ; 2 ; 3 ; 2 ; 3 ] : Multiset<int>) |])
                 .Returns(5)
                 .SetName("A non-disjoint mset's length is correct") ]

        /// <summary>
        ///     Tests <c>Multiset.length</c>.
        /// </summary>
        [<TestCaseSource("MultisetLength")>]
        member x.``Multiset.length takes multiset length correctly`` (a : Multiset<int>) =
            Multiset.length a
