/// <summary>
///     The dreaded 'miscellaneous functions' module.
///
///     <para>
///         Most of these are generic, stand-alone combinators, but some
///         also augment Chessie and other libraries.
///     </para>
/// </summary>
[<AutoOpen>]
module Starling.Utils

open CommandLine

open Chessie.ErrorHandling

module Config =
    /// Command-line flags used in the Starling executable.
    [<NoComparison>]
    type Options =
        { [<Option(
                'r',
                HelpText =
                    "Dump results in raw format instead of pretty-printing.")>]
          raw : bool
          [<Option(
                'B',
                HelpText =
                    "Comma-delimited set of backend options (pass 'list' for details)")>]
          backendOpts : string option
          [<Option(
                's',
                HelpText =
                    "The stage at which Starling should stop and output.")>]
          stage : string option
          [<Option(
                't',
                HelpText =
                    "Show specific axiom or term in term-refinement stages.")>]
          term : string option
          [<Option('m', HelpText = "Show full model in term-refinement stages.")>]
          showModel : bool
          [<Option('O', HelpText = "Switches given optimisations on or off.")>]
          optimisers : string option
          [<Option("times", HelpText = "Print times for each phase.")>]
          times : bool
          [<Option('v', HelpText = "Increases verbosity.")>]
          verbose : bool
          [<Option('c', HelpText = "Enable color printing")>]
          color : bool
          [<Value(
                0,
                MetaName = "input",
                HelpText =
                    "The file to load (omit, or supply -, for standard input).")>]
          input : string option }

    let _emptyOpts = {
        raw             = false;
        backendOpts     = None;
        stage           = None;
        term            = None;
        showModel       = false;
        optimisers      = None;
        times           = false;
        verbose         = false;
        input           = None;
        color           = false;
    }

    let _configRef = ref _emptyOpts
    let config () = ! _configRef

/// <summary>
///     Parses an delimited option string.
/// </summary>
/// <param name="str">
///     A string containing a comma or semicolon-separated list of words.
/// </param>
/// <returns>
///     The sequence of split words, downcased and trimmed.
///     A tuple of two sets of optimisation names.  The first is the
///     set of optimisations force-disabled (-).  The second is the set of
///     optimisations force-enabled (+ or no sign).  Each optimisation
///     name is downcased.  The optimisation name 'all' is special, as it
///     force-enables (or force-disables) all optimisations.
/// </returns>
let parseOptionString (str : string) =
    str.ToLower()
        .Split([| "," ; ";" |],
               System.StringSplitOptions.RemoveEmptyEntries)
    |> Seq.toList
    |> Seq.map (fun x -> x.Trim())


/// Converts a list to an option that is Some iff it has exactly one item.
let onlyOne s =
    s
    |> List.ofSeq
    |> function
       | [x] -> Some x
       | _ -> None

/// Reverses a 2-argument function.
let flip f x y = f y x

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

(*
 * Map data structure
 *)

/// Tries to find duplicate entries in a list.
/// Returns a list of the duplicates found.
let findDuplicates lst =
    lst
    |> Seq.groupBy id
    |> Seq.choose
           // dupes now contains all of the appearances of x.
           // If we can successfully take 2 appearances, it's a duplicate.
           (function
            | (x, dupes) when dupes |> Seq.truncate 2 |> Seq.length = 2
                -> Some x
            | _ -> None)

/// Returns the keys of a map as a sequence.
let keys mp =
    mp |> Map.toSeq |> Seq.map fst

/// Returns the duplicate keys across two maps.
let keyDuplicates a b =
    findDuplicates (Seq.append (keys a) (keys b))

/// <summary>
///     Behaves like a combination of <c>List.map</c> and
///     <c>List.fold</c>.
/// </summary>
/// <param name="f">
///     The mapping function.
/// </param>
/// <param name="init">
///     The initial accumulator.
/// </param>
/// <param name="lst">
///     The list to map.
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
///     A tuple of the final accumulator and mapped list.
/// </returns>
let mapAccumL
  (f : 'acc -> 'src -> ('acc * 'dst))
  (init : 'acc)
  (lst : 'src list)
  : ('acc * 'dst list) =
    let rec it acc srcs dsts =
        match srcs with
        | [] -> (acc, List.rev dsts)
        | x::xs ->
            let acc', x' = f acc x
            it acc' xs (x'::dsts)
    it init lst []

/// Joins two maps together.
let mapAppend a b =
    Map.ofSeq (Seq.append (Map.toSeq a) (Map.toSeq b))

(*
 * Chessie-related functions.
 *)

/// Extends lift to functions of 3 arguments.
let lift3 f a b c =
    trial { let! av = a
            let! bv = b
            let! cv = c
            return f av bv cv }

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

/// Performs f on x, but wraps each failure e to g(x, e).
let wrapMessages g f x = x |> f |> mapMessages (curry g x)

/// Performs f on x and y, but wraps each failure e to g(x, y, e).
let wrapMessages2 g f x y = f x y |> mapMessages (curry3 g x y)

/// Like fold, but constantly binds the given function over a Chessie result.
/// The initial state is wrapped in 'ok'.
let seqBind f initialS = Seq.fold (fun s x -> bind (f x) s) (ok initialS)


/// Fold that can be terminated earlier by the step function f returning None.
/// If Any step returns None, the whole fold returns None.
let foldFastTerm (f : 'State -> 'T -> 'State option)
                 (s : 'State) (l : 'T seq) =
    let en = l.GetEnumerator()

    let rec fft f s' =
        if (en.MoveNext())
        then match f s' en.Current with
             | Some s'' -> fft f s''
             | None -> None
        else (Some s')

    fft f s

/// Repeatedly apply f until a fixed point is reached
let fix_bound = ref -1
let fix f v =
    let rec fixiter f v0 v1 n =
        if v0 = v1 || (n >= !fix_bound && !fix_bound > 0) then v0 else fixiter f v1 (f v1) (n + 1)
    fixiter f v (f v) 0


/// <summary>
///    Utilities for testing.
/// </summary>
module Testing =
    open NUnit.Framework

    /// <summary>
    ///     A more F#-friendly overload of <c>TestCaseData</c>.
    /// </summary>
    let tcd : obj[] -> TestCaseData = TestCaseData

    module TestFix =
        let inc = (+) 1
        let cnst x _ = x

        let check bound out =
            fix_bound := bound
            Assert.AreEqual (out, fix inc 0)

        [<Test>]
        let ``test fix bounding`` () =
            // check that (inc (inc (inc (0)))) = 3
            check 3 3

        [<Test>]
        let ``test fix fix-point`` () =
            // check that inc (inc (inc (0))) = 3
            Assert.AreEqual (3, fix (cnst 3) 0)
