/// A simple multiset type.
module Starling.Multiset

type Multiset<'a> = 'a list

/// Creates a new empty multiset.
let empty () = []

/// Creates a new multiset with the given list as its contents.
let fromList xs =
    List.sort xs

/// Appends two multisets.
let append xs ys =
    /// TODO(CaptainHayashi): a more efficient algorithm for this.
    List.sort (List.append xs ys)

/// Converts a multiset back to a list.
let toList = id
