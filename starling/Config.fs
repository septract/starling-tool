/// The Starling executable's command-line configuration.
module Starling.Cli.Config

open CommandLine

/// Command-line flags used in the Starling executable.
[<NoComparison>]
type Options =
    {
        [<Option(
            'B',
            Default = "",
            HelpText =
                "Comma-delimited set of backend options (pass 'list' for details)")>]
        backendOpts : string
        [<Option(
            's',
            Default = "",
            HelpText =
                "The stage at which Starling should stop and output.")>]
        stage : string
        [<Option(
            't',
            Default = "",
            HelpText =
                "Show specific axiom or term in term-refinement stages.")>]
        term : string
        [<Option('m', HelpText = "Show full model in term-refinement stages.")>]
        showModel : bool
        [<Option(
            'O',
            Default = "",
            HelpText = "Switches given optimisations on or off.")>]
        optimisers : string
        [<Option(
            'V',
            Default = "",
            HelpText =
                "Comma-delimited set of output options (pass 'list' for details)")>]
        viewOpts : string
        [<Option('v', HelpText = "Increases verbosity.")>]
        verbose : bool
        [<Option(
            'P',
            Default = "",
            HelpText =
                "Comma-delimited set of profiling options (pass 'list' for details")>]
        profilerFlags : string
        [<Value(
            0,
            (* Use "" here, not "-", to make sure Starling prints a 'reading
               from stdin' message. *)
            Default = "",
            MetaName = "input",
            HelpText =
                "The file to load (omit, or supply -, for standard input).")>]
        input : string }

let _emptyOpts : Options = {
    backendOpts     = "";
    stage           = "";
    term            = "";
    showModel       = false;
    optimisers      = "";
    viewOpts        = "";
    verbose         = false;
    profilerFlags   = "";
    input           = "";
}

let _configRef : Options ref = ref _emptyOpts
let config () : Options = ! _configRef

/// <summary>
///     Parses an delimited option string.
/// </summary>
/// <param name="str">
///     A string containing a comma or semicolon-separated list of words.
///     May be null or empty.
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
    if str = null || str = ""
    then Seq.empty
    else
        str.ToLower()
            .Split([| "," ; ";" |],
                   System.StringSplitOptions.RemoveEmptyEntries)
        |> Seq.toList
        |> Seq.map (fun x -> x.Trim())
