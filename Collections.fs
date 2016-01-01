/// Collections used in Starling.
module Starling.Collections

/// A function-like construct.
type Func<'a> =
    { Name: string
      Params: 'a list }

/// A multiset, or ordered list.
type Multiset<'a> = 
    | MSet of 'a list

module Multiset = 
    (*
     * Construction
     *)

    /// Creates a new empty multiset.
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

    /// Appends two multisets.
    let append xs ys = 
        /// TODO(CaptainHayashi): a more efficient algorithm for this.
        Seq.append (toSeq xs) (toSeq ys) |> ofSeq
    
    /// Maps over a multiset.
    /// Since multisets are ordered, mapping can change the position of items.
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
