/// The dreaded 'miscellaneous functions' module.
///
/// Most of these are generic, stand-alone combinators, but some also
/// augment Chessie and other libraries.
[<AutoOpen>]
module Starling.Utils

open Chessie.ErrorHandling

/// Passes fst through f, and snd through s.
let pairMap f s p = (f (fst p), s (snd p))

/// Converts a pairwise function to a function of two arguments.
let curry f a b = f (a, b)

/// Converts a triple-wise function to a function of three arguments.
let curry3 f a b c = f (a, b, c)

/// Converts a function of two arguments to a pairwise function.
let uncurry f ab = f (fst ab) (snd ab)

/// Constructs a pair from left to right.
let mkPair x y = (x, y)

/// List cons (::) as a two-argument function.
let cons a b = a :: b

/// Maps a function f through a set, and concatenates the resulting
/// list of lists into one set.
let unionMap f xs =
    // Adapted from the GHC base implementation,
    // see http://hackage.haskell.org/package/base-4.8.1.0/docs/src/Data.Foldable.html
    // for source and copyright information.
    xs
    |> Set.toSeq
    |> Seq.map f
    |> Set.unionMany


/// Maps a function f through a list, and concatenates the resulting
/// list of lists into one list.
let concatMap f xs =
    // Adapted from the GHC base implementation,
    // see http://hackage.haskell.org/package/base-4.8.1.0/docs/src/Data.Foldable.html
    // for source and copyright information.
    List.foldBack (fun x b -> List.foldBack cons (f x) b) xs []

/// Tries to find duplicate entries in a list.
/// Returns a list of the duplicates found.
let findDuplicates lst =
    lst
    |> List.groupBy id
    |> List.choose (function
                    | ( _, [] ) | ( _, [_] ) -> None
                    | ( x, _ ) -> Some x)

//
// Chessie-related functions.
//

/// If both sides of a pair are ok, return f applied to them.
/// Else, return the errors.
let pairBindMap f g lr =
    trial { let! l = f (fst lr)
            let! r = f (snd lr)
            return g (l, r) }

/// Maps f over e's messages.
let mapMessages f =
    either (fun pair -> Ok (fst pair, List.map f (snd pair)))
           (fun msgs -> List.map f msgs |> Bad)

