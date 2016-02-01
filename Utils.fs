/// The dreaded 'miscellaneous functions' module.
///
/// Most of these are generic, stand-alone combinators, but some also
/// augment Chessie and other libraries.
[<AutoOpen>]
module Starling.Utils

open Chessie.ErrorHandling

/// Converts a list to an option that is Some iff it has exactly one item.
let onlyOne s =
    s
    |> List.ofSeq
    |> function
       | [x] -> Some x
       | _ -> None

/// Reverses a pair.
let flipPair (x, y) = (y, x)

/// A predicate that always returns true.
let always _ = true

/// Applies f and g to x and returns (f x, g x).
let splitThrough f g x = (f x, g x)

/// Given f and x, returns (x, f x).
let inAndOut f = splitThrough id f

/// Given f and (x, y), returns (x, f x y).
let inAndOut2 f (x, y) = (x, f x y)

/// Passes fst through f, and snd through g.
let pairMap f g = splitThrough (fst >> f) (snd >> g)

/// Converts a pairwise function to a function of two arguments.
let curry f a b = f (a, b)

/// Converts a triple-wise function to a function of three arguments.
let curry3 f a b c = f (a, b, c)

/// Converts a function of two arguments to a pairwise function.
let uncurry f (a, b) = f a b

/// Constructs a pair from left to right.
let mkPair x y = (x, y)

/// List cons (::) as a two-argument function.
let cons a b = a :: b

/// Puts a onto the top of a sequence b.
let scons a = Seq.append (Seq.singleton a)

/// Returns `a` if the input is `Some a`, or `d` otherwise.
let withDefault d =
    function
    | Some a -> a
    | None -> d

/// Maps a function f through a set, and concatenates the resulting
/// list of lists into one set.
let unionMap f = 
    Set.toSeq
    >> Seq.map f
    >> Set.unionMany

/// Maps a function f through a list, and concatenates the resulting
/// list of lists into one list.
let concatMap f xs = 
    (* Adapted from the GHC base implementation,
     * see http://hackage.haskell.org/package/base-4.8.1.0/docs/src/Data.Foldable.html
     * for source and copyright information.
     *)
    List.foldBack (fun x b -> List.foldBack cons (f x) b) xs []

/// Tries to find duplicate entries in a list.
/// Returns a list of the duplicates found.
let findDuplicates lst = 
    lst
    |> List.groupBy id
    |> List.choose (function 
           | (_, []) | (_, [ _ ]) -> None
           | (x, _) -> Some x)

(*
 * Chessie-related functions.
 *)

/// Converts a Result into an option with Some x if the result was Ok x _.
let okOption =
    function
    | Ok (x, _) -> Some x
    | _ -> None

/// Converts a Result into an option with Some x if the result was Fail x _.
let failOption =
    function
    | Fail xs -> Some xs
    | _ -> None

/// Maps f over e's messages.
let mapMessages f = either (fun (v, msgs) -> Ok(v, List.map f msgs)) (fun msgs -> List.map f msgs |> Bad)

/// Like fold, but constantly binds the given function over a Chessie result.
/// The initial state is wrapped in 'ok'.
let seqBind f initialS = Seq.fold (fun s x -> bind (f x) s) (ok initialS)


/// Fold that can be terminated earlier by the step function f returning None.
/// If Any step returns None, the whole fold returns None.
let rec foldFastTerm  (f : 'State -> 'T -> 'State option)  (s : 'State) (l : 'T list) =  
     match l with 
     | []   -> Some s
     | x::l -> 
        match f s x with 
        | Some s -> foldFastTerm f s l
        | None -> None 