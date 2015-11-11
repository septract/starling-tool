namespace Starling

open Chessie.ErrorHandling

/// The dreaded 'miscellaneous functions' module.
///
/// Most of these are generic, stand-alone combinators, but some also
/// augment Chessie and other libraries.
[<AutoOpen>]
module Utils =
    /// Passes fst through f, and snd through s.
    let pairMap f s p = ( f ( fst p ) , s ( snd p ) )

    /// Converts a pairwise function to a function of two arguments.
    let curry f a b = f ( a, b )

    /// Converts a triple-wise function to a function of three arguments.
    let curry3 f a b c = f ( a, b, c )

    /// Converts a function of two arguments to a pairwise function.
    let uncurry f ab = f ( fst ab ) ( snd ab )
