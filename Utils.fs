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
          [<Option(
                'V',
                HelpText =
                    "Comma-delimited set of output options (pass 'list' for details)")>]
          viewOpts : string option
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

    let _emptyOpts : Options = {
        raw             = false;
        backendOpts     = None;
        stage           = None;
        term            = None;
        showModel       = false;
        optimisers      = None;
        viewOpts        = None;
        times           = false;
        verbose         = false;
        input           = None;
        color           = false;
    }

    let _configRef : Options ref = ref _emptyOpts
    let config () : Options = ! _configRef

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
let parseOptionString (str : string) : string seq =
    str.ToLower()
        .Split([| "," ; ";" |],
               System.StringSplitOptions.RemoveEmptyEntries)
    |> Seq.toList
    |> Seq.map (fun x -> x.Trim())


/// <summary>
///     Converts a sequence to an option that is <c>Some</c> iff it has exactly
///     one item.
/// </summary>
/// <param name="s">
///     The sequence to convert.
/// </param>
/// <typeparam name="a">
///     The type of elements in the sequence.
/// </typeparam>
/// <returns>
///     An <see cref="Option"/> that is <c>Some> iff <paramref name="s"/> has
///     exactly one item.
/// </returns>
let onlyOne (s : 'A seq) : 'A option =
    s
    |> List.ofSeq
    |> function
       | [x] -> Some x
       | _ -> None

/// Reverses a 2-argument function.
let flip (f : 'A -> 'B -> 'C) (x : 'B) (y : 'A) : 'C = f y x

/// A predicate that always returns true.
let always (_ : _) : bool = true

/// Passes fst through f, and snd through g.
let pairMap (f : 'A1 -> 'B1) (g : 'A2 -> 'B2) (a1 : 'A1, a2 : 'A2) : 'B1 * 'B2 =
    (f a1, g a2)

/// Converts a pairwise function to a function of two arguments.
let curry (f : 'A * 'B -> 'C) (a : 'A) (b : 'B) : 'C = f (a, b)

/// Converts a triple-wise function to a function of three arguments.
let curry3 (f : 'A * 'B * 'C -> 'D) (a : 'A) (b : 'B) (c : 'C) : 'D =
    f (a, b, c)

/// Converts a function of two arguments to a pairwise function.
let uncurry (f : 'A -> 'B -> 'C) (a : 'A, b : 'B) : 'C = f a b

/// Constructs a pair from left to right.
let mkPair (a : 'A) (b : 'B) : 'A * 'B = (a, b)

/// List cons (::) as a two-argument function.
let cons (x : 'X) (xs : 'X list) : 'X list = x :: xs

/// Puts a onto the top of a sequence b.
let scons (x : 'X) : 'X seq -> 'X seq = Seq.append (Seq.singleton x)

/// <summary>
///     Returns a default value if the input is <c>None</c>, and maps a function
///     over it otherwise.
/// </summary>
/// <param name="d">The default value.</param>
/// <param name="f">The transformer used if the input is <c>Some</c>.</param>
/// <param name="input">The input value.</param>
/// <typeparam name="In">The type of the input.</typeparam>
/// <typeparam name="Out">The type of the input.</typeparam>
/// <returns>
///     <paramref name="d"/> if <paramref name="input"/> is <c>None</c>;
///     <paramref name="f"/> <c>v</c> if it is <c>Some v</c>.
/// </returns>
let maybe (d : 'Out) (f : 'In -> 'Out) (input: 'In option) : 'Out =
    match input with
    | Some a -> f a
    | None -> d

/// Returns `a` if the input is `Some a`, or `d` otherwise.
let withDefault (d : 'A) : 'A option -> 'A = maybe d id

/// Maps a function f through a sequence, and concatenates the resulting
/// list of lists into one set.
let unionMap (f : 'A -> Set<'B>) : 'A seq -> Set<'B> =
    Seq.map f >> Set.unionMany

/// Maps a function f through a list, and concatenates the resulting
/// list of lists into one list.
let concatMap (f : 'A -> 'B list) (xs : 'A list) : 'B list =
    (* Adapted from the GHC base implementation,
     * see http://hackage.haskell.org/package/base-4.8.1.0/docs/src/Data.Foldable.html
     * for source and copyright information.
     *)
    List.foldBack (fun x b -> List.foldBack cons (f x) b) xs []

(*
 * Map data structure
 *)

/// Tries to find duplicate entries in a sequence.
/// Returns a sequence of the duplicates found.
let findDuplicates (s : 'A seq) : 'A seq =
    s
    |> Seq.groupBy id
    |> Seq.choose
           // dupes now contains all of the appearances of x.
           // If we can successfully take 2 appearances, it's a duplicate.
           (function
            | (x, dupes) when dupes |> Seq.truncate 2 |> Seq.length = 2
                -> Some x
            | _ -> None)

/// Returns the keys of a map as a sequence.
let keys (mp : Map<'Key, _>) : 'Key seq =
    mp |> Map.toSeq |> Seq.map fst

/// Returns the duplicate keys across two maps.
let keyDuplicates (a : Map<'Key, _>) (b : Map<'Key, _>) : 'Key seq =
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
/// <typeparam name="Src">
///     The type of variables in the list to map.
/// </typeparam>
/// <typeparam name="Dst">
///     The type of variables in the list after mapping.
/// </typeparam>
/// <returns>
///     A tuple of the final accumulator and mapped list.
/// </returns>
let mapAccumL
  (f : 'Acc -> 'Src -> ('Acc * 'Dst))
  (init : 'Acc)
  (lst : 'Src list)
  : ('Acc * 'Dst list) =
    let rec it acc srcs dsts =
        match srcs with
        | [] -> (acc, List.rev dsts)
        | x::xs ->
            let acc', x' = f acc x
            it acc' xs (x'::dsts)
    it init lst []

/// Joins two maps together.
let mapAppend (a : Map<'Key, 'Value>) (b : Map<'Key, 'Value>)
  : Map<'Key, 'Value> =
    Map.ofSeq (Seq.append (Map.toSeq a) (Map.toSeq b))

(*
 * Chessie-related functions.
 *)

/// Extends bind to functions of 2 arguments.
let bind2
  (f: 'A -> 'B -> Result<'Value, 'Error>)
  (a : Result<'A, 'Error>)
  (b : Result<'B, 'Error>)
  : Result<'Value, 'Error> =
    trial { let! av = a
            let! bv = b
            return! f av bv }

/// Extends bind to functions of 3 arguments.
let bind3
  (f: 'A -> 'B -> 'C -> Result<'Value, 'Error>)
  (a : Result<'A, 'Error>)
  (b : Result<'B, 'Error>)
  (c : Result<'C, 'Error>)
  : Result<'Value, 'Error> =
    trial { let! av = a
            let! bv = b
            let! cv = c
            return! f av bv cv }

/// Extends bind to functions of 4 arguments.
let bind4
  (f: 'A -> 'B -> 'C -> 'D -> Result<'Value, 'Error>)
  (a : Result<'A, 'Error>)
  (b : Result<'B, 'Error>)
  (c : Result<'C, 'Error>)
  (d : Result<'D, 'Error>)
  : Result<'Value, 'Error> =
    trial { let! av = a
            let! bv = b
            let! cv = c
            let! dv = d
            return! f av bv cv dv }

/// Extends lift to functions of 3 arguments.
let lift3
  (f: 'A -> 'B -> 'C -> 'Value)
  (a : Result<'A, 'Error>)
  (b : Result<'B, 'Error>)
  (c : Result<'C, 'Error>)
  : Result<'Value, 'Error> =
    trial { let! av = a
            let! bv = b
            let! cv = c
            return f av bv cv }

/// Extends lift to functions of 4 arguments.
let lift4
  (f: 'A -> 'B -> 'C -> 'D -> 'Value)
  (a : Result<'A, 'Error>)
  (b : Result<'B, 'Error>)
  (c : Result<'C, 'Error>)
  (d : Result<'D, 'Error>)
  : Result<'Value, 'Error> =
    trial { let! av = a
            let! bv = b
            let! cv = c
            let! dv = d
            return f av bv cv dv }

/// Converts a Result into an option with Some x if the result was Ok x _.
let okOption : Result<'Value, _> -> 'Value option =
    function
    | Ok (x, _) -> Some x
    | _ -> None

/// Converts a Result into an option with Some x if the result was Fail x _.
let failOption : Result<_, 'Error> -> 'Error list option =
    function
    | Fail xs -> Some xs
    | _ -> None

/// Maps f over e's messages.
let mapMessages (f : 'Error1 -> 'Error2)
  : Result<_, 'Error1> -> Result<_, 'Error2> =
    either
        (fun (v, msgs) -> Ok(v, List.map f msgs))
        (fun msgs -> List.map f msgs |> Bad)

/// Performs f on x, but wraps each failure e to g(x, e).
let wrapMessages
  (g : 'A * 'Error1 -> 'Error2)
  (f : 'A -> Result<'Value, 'Error1>)
  (x : 'A)
  : Result<'Value, 'Error2> =
    x |> f |> mapMessages (curry g x)

/// Performs f on x and y, but wraps each failure e to g(x, y, e).
let wrapMessages2
  (g : 'A * 'B * 'Error1 -> 'Error2)
  (f : 'A -> 'B -> Result<'Value, 'Error1>)
  (x : 'A)
  (y : 'B)
  : Result<'Value, 'Error2> =
    f x y |> mapMessages (curry3 g x y)

/// Like fold, but constantly binds the given function over a Chessie result.
/// The initial state is wrapped in 'ok'.
let seqBind
  (f : 'T -> 'State -> Result<'State, 'Error>)
  (initialS: 'State)
  : 'T seq -> Result<'State, 'Error> =
    Seq.fold (fun s x -> bind (f x) s) (ok initialS)


/// Fold that can be terminated earlier by the step function f returning None.
/// If Any step returns None, the whole fold returns None.
let foldFastTerm
  (f : 'State -> 'T -> 'State option)
  (s : 'State) (l : 'T seq)
  : 'State option =
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

    let assertEqual (a : 'a) (b : 'a) = Assert.AreEqual(a, b)
    let AssertAreEqual(a, b) = assertEqual a b

    /// <summary>
    ///     Asserts that a Chessie result failed with a given result list.
    /// </summary>
    let assertFail
      (expected: 'Error list)
      (actualResult : Result<'Val, 'Error>)
      (pVal : 'Val -> string)
      : unit =
        match actualResult with
        | Fail actuals ->
            assertEqual (List.sort expected) (List.sort actuals)
        | Warn (v, _) | Pass v ->
            let fmsg = sprintf "Got successful result:\n%s" (pVal v)
            Assert.Fail(fmsg)


    let assertOkAndEqual
      (expected: 'Val)
      (actualResult : Result<'Val, 'Error>)
      (pError : 'Error -> string)
      : unit =
        match actualResult with
        | Pass actual -> assertEqual expected actual
        | Warn (_, warns) | Fail warns ->
            let warnstr = String.concat "\n" (List.map pError warns)
            let fmsg = sprintf "Got errors:\n%s" warnstr
            Assert.Fail(fmsg)

    let inline (?=?) a b = assertEqual a b

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
