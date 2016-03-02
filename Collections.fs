/// Collections used in Starling.
module Starling.Collections

/// <summary>
///     A tagged item.
/// </summary>
/// <typeparam name="a">
///     The type of the item being tagged.
/// </typeparam>
type Tagged<'a> =
    { /// <summary>
      ///     The tag, as a list of strings.
      /// </summary>
      Tag : string list

      /// <summary>
      ///     The tagged item.
      /// </summary>
      Item : 'a }

/// <summary>
///   Operations on tagged items.
/// </summary>
module Tagged =
    /// <summary>
    ///     Tags an item.
    /// </summary>
    /// <param name="tag">
    ///     The tag to attach to <paramref name="item" />.
    /// </param>
    /// <param name="item">
    ///     The item to tag.
    /// </param>
    /// <returns>
    ///     The <c>Tagged</c> instance resulting from tagging
    ///     <paramref name="item" /> with <paramref name="tag" />.
    /// </returns>
    let tag tag item = { Tag = tag ; Item = item }

    /// <summary>
    ///     Maps functions over the tag and item of a tagged item.
    /// </summary>
    /// <param name="f">
    ///     The function to map over the tag.
    /// </param>
    /// <param name="g">
    ///     The function to map over the item.
    /// </param>
    /// <param name="_arg1">
    ///     The <c>Tagged</c> to map.
    /// </param>
    /// <returns>
    ///     The <c>Tagged</c> instance resulting from mapping
    ///     <paramref name="f" /> and <paramref name="g" /> over
    ///     <paramref name="_arg1" />.
    /// </returns>
    let map f g { Tag = tag ; Item = item } =
        { Tag = f tag ; Item = g item }

    /// <summary>
    ///     Converts a tagged sequence of items to a sequence of tagged items.
    ///
    ///     <para>
    ///         Each item inherits the parent's tag, with a string
    ///         representation of its index in the sequence prepended.
    ///     </para>
    /// </summary>
    /// <param name="_arg1" />
    ///     The tagged sequence of items to break up.
    /// </param>
    /// <returns>
    ///     A sequence containing the items from <paramref name="_arg1" />
    ///     individually tagged.
    /// </returns>
    let split { Tag = tag; Item = xs } =
        Seq.mapi (fun i x -> { Tag = (sprintf "%d" i) :: tag ; Item = x })


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
///   Creates a new <c>Func</c>.
/// </summary>
/// <parameter name="name">
///   The name of the <c>Func</c>.
/// </parameter>
/// <parameter name="pars">
///   The parameters of the <c>Func</c>, as a sequence.
/// </parameter>
/// <returns>
///   A new <c>Func</c> with the given name and parameters.
/// </returns>
let func name pars = { Name = name; Params = List.ofSeq pars }

/// <summary>
///   A multiset, or ordered list.
/// </summary>
/// <typeparam name="item">The type of items in the Multiset.</typeparam>
type Multiset<'item> = 
    | MSet of 'item list

/// <summary>
///   Operations on multisets.
/// </summary>
/// <seealso cref="T:Starling.Collections.Multiset`1" />
module Multiset = 
    (*
     * Construction
     *)

    /// Creates a new, empty multiset.
    let empty() = MSet []
    
    /// Creates a new singleton multiset.
    let singleton x = MSet [ x ]
    
    /// Creates a new multiset with the given list as its contents.
    let ofList xs = 
        xs
        |> List.sort
        |> MSet
    
    /// Creates a new multiset with the given sequence as its contents.
    let ofSeq xs = 
        xs
        |> Seq.sort
        |> Seq.toList
        |> MSet
    
    (*
     * Destruction
     *)

    /// Converts a multiset to a sorted list.
    let toList = function 
        | MSet xs -> xs
    
    /// Converts a multiset to a sorted seq.
    let toSeq ms = 
        ms
        |> toList
        |> List.toSeq
    
    /// Converts a multiset to a set, removing duplicates.
    let toSet ms = 
        ms
        |> toList
        |> Set.ofList
    
    (*
     * Operations
     *)

    /// <summary>
    ///   Appends two multisets.
    /// </summary>
    /// <remarks>
    ///   Since multisets are ordered, the resulting multiset may not
    ///   necessarily be <c>xs</c> followed by <c>ys</c>.
    /// </remarks>
    ///
    /// <param name="xs">The first multiset to append.</param>
    /// <param name="ys">The second multiset to append.</param>
    ///
    /// <returns>
    ///   The result of appending <c>xs</c> to <c>ys</c>.
    /// </returns>
    let append xs ys = 
        // TODO(CaptainHayashi): a more efficient algorithm for this.
        Seq.append (toSeq xs) (toSeq ys) |> ofSeq
    
    /// <summary>
    ///   Maps <c>f</c> over a multiset.
    /// </summary>
    /// <remarks>
    ///   Since multisets are ordered, mapping can change the position of items.
    /// </remarks>
    ///
    /// <param name="f">The function to map over the multiset.</param>
    ///
    /// <returns>
    ///   The result of mapping <c>f</c> over the multiset.
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
