/// The dreaded 'miscellaneous functions' module.
///
/// Most of these are generic, stand-alone combinators, but some also
/// augment Chessie and other libraries.
[<AutoOpen>]
module Starling.Utils

open Chessie.ErrorHandling

/// Passes fst through f, and snd through s.
let pairMap f s p = ( f ( fst p ) , s ( snd p ) )

/// Converts a pairwise function to a function of two arguments.
let curry f a b = f ( a, b )

/// Converts a triple-wise function to a function of three arguments.
let curry3 f a b c = f ( a, b, c )

/// Converts a function of two arguments to a pairwise function.
let uncurry f ab = f ( fst ab ) ( snd ab )

/// Constructs a pair from left to right.
let mkPair x y = (x, y)

//
// Chessie-related functions.
//

/// If both sides of a pair are ok, return f applied to them.
/// Else, return the errors.
let pairBindMap f g lr =
    trial {
        let! l = f ( fst lr )
        let! r = f ( snd lr )
        return g ( l, r )
    }

/// Maps f over e's messages.
let mapMessages f =
    either ( fun pair -> Ok ( fst pair, List.map f ( snd pair ) ) )
           ( fun msgs -> List.map f msgs |> Bad )

