/// <summary>
///     Module defining view (and func) definers.
/// </summary>
module Starling.Core.Definer

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.TypeSystem
open Starling.Core.TypeSystem.Check


/// <summary>
///     A definer function mapping views to their meanings.
/// </summary>
/// <typeparam name="defn">
///     Type of definitions of <c>View</c>s stored in the table.
///     May be <c>unit</c>.
/// </typeparam>
type ViewDefiner<'defn> =
    // TODO(CaptainHayashi): this should probably be a map,
    // but translating it to one seems non-trivial.
    // Would need to define equality on funcs very loosely.
    (DView * 'defn) list

/// <summary>
///     A definer function mapping funcs to their meanings.
/// </summary>
/// <typeparam name="defn">
///     Type of definitions of <c>Func</c>s stored in the table.
///     May be <c>unit</c>.
/// </typeparam>
type FuncDefiner<'defn> =
    // TODO(CaptainHayashi): this should probably be a map,
    // but translating it to one seems non-trivial.
    // Would need to define equality on funcs very loosely.
    (DFunc * 'defn) list

/// <summary>
///     Type of errors encountered when using definers.
/// </summary>
type Error =
    /// <summary>
    ///     The func looked up has a parameter <c>param</c>, which
    ///     has been assigned to an argument of the incorrect type
    ///     <c>atype</c>.
    /// </summary>
    | TypeMismatch of param: TypedVar * atype: Type
    /// <summary>
    ///     The func looked up has <c>fn</c> arguments, but its
    ///     definition has <c>dn</c> parameters.
    /// </summary>
    | CountMismatch of fn: int * dn: int


module FuncDefiner =
    /// <summary>
    ///     Converts a <c>FuncDefiner</c> to a sequence of pairs of
    ///     <c>Func</c> and definition.
    /// </summary>
    /// <param name="definer">
    ///     A <see cref="FuncDefiner"/> to convert to a sequence.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of <c>Func</c> definitions.  May be <c>unit</c>.
    /// </typeparam>
    /// <returns>
    ///     The sequence of (<c>Func</c>, <c>'defn</c>) pairs.
    ///     A <c>FuncDefiner</c> allowing the <c>'defn</c>s of the given
    ///     <c>Func</c> to be looked up.
    /// </returns>
    let toSeq (definer : FuncDefiner<'defn>) : (DFunc * 'defn) seq =
        // This function exists to smooth over any changes in Definer
        // representation we make later (eg. to maps).
        List.toSeq definer

    /// <summary>
    ///     Builds a <c>FuncDefiner</c> from a sequence of pairs of
    ///     <c>Func</c> and definition.
    /// </summary>
    /// <param name="fseq">
    ///     The sequence of (<c>Func</c>, <c>'defn</c>) pairs.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of <c>Func</c> definitions.  May be <c>unit</c>.
    /// </typeparam>
    /// <returns>
    ///     A <c>FuncDefiner</c> allowing the <c>'defn</c>s of the given
    ///     <c>Func</c> to be looked up.
    /// </returns>
    let ofSeq (fseq : #((DFunc * 'defn) seq)) : FuncDefiner<'defn> =
        // This function exists to smooth over any changes in Definer
        // representation we make later (eg. to maps).
        Seq.toList fseq

    /// <summary>
    ///     Checks whether <c>func</c> and <c>_arg1</c> agree on parameter
    ///     count.
    /// </summary>
    /// <param name="func">
    ///     The func being looked up, the process of which this check is part.
    /// </param>
    /// <param name="_arg1">
    ///     An <c>Option</c>al pair of <c>DFunc</c> and its defining
    ///     <c>BoolExpr</c>.
    ///     The value <c>None</c> suggests that <c>func</c> has no definition,
    ///     which can be ok (eg. if the <c>func</c> is a non-defining view).
    /// </param>
    /// <returns>
    ///     A Chessie result, where the <c>ok</c> value is the optional pair of
    ///     prototype func and definition, and the failure value is a
    ///     <c>Starling.Core.Definer.Error</c>.
    /// </returns>
    let checkParamCount (func : Func<'a>) : (Func<'b> * 'c) option -> Result<(Func<'b> * 'c) option, Error> =
        function
        | None -> ok None
        | Some def ->
            let fn = List.length func.Params
            let dn = List.length (fst def).Params
            if fn = dn then ok (Some def) else CountMismatch (fn, dn) |> fail

    /// <summary>
    ///     Checks whether <c>func</c> and <c>_arg1</c> agree on parameter
    ///     types.
    /// </summary>
    /// <param name="func">
    ///     The func being looked up, the process of which this check is part.
    /// </param>
    /// <param name="def">
    ///     The <c>DFunc</c> that <paramref name="func" /> has matched.
    /// </param>
    /// <returns>
    ///     A Chessie result, where the <c>ok</c> value is
    ///     <paramref name="func" />, and the failure value is a
    ///     <c>Starling.Core.Definer.Error</c>.
    /// </returns>
    let checkParamTypes func def =
        List.map2
            (curry
                 (function
                  | UnifyInt _ | UnifyBool _ -> ok ()
                  | UnifyFail (fp, dp) -> fail (TypeMismatch (dp, typeOf fp))))
            func.Params
            def.Params
        |> collect
        |> lift (fun _ -> func)

    /// <summary>
    ///     Look up <c>func</c> in <c>_arg1</c>.
    ///
    ///     <para>
    ///         This checks that the use of <c>func</c> agrees on the number of
    ///         parameters, but not necessarily types.  You will need to add
    ///         type checking if needed.
    ///     </para>
    /// </summary>
    /// <param name="func">The func to look up in <c>definer</c>.</param>
    /// <param name="definer">
    ///     A definer mapping <c>Func</c>s to some definition.
    /// </param>
    /// <typeparam name="Defn">The type of definer definitions.</typeparam>
    /// <returns>
    ///     A Chessie result, where the <c>ok</c> value is an <c>Option</c>
    ///     containing the pair of
    ///     prototype func and definition, and the failure value is a
    ///     <c>Starling.Core.Definer.Error</c>.  If the <c>ok</c> value is
    ///     <c>None</c>, it means no (valid or otherwise) definition exists.
    /// </returns>
    let lookup (func : Func<_>) (definer : FuncDefiner<'Defn>)
      : Result<(DFunc * 'Defn) option, Error> =
        // First, try to find a func whose name agrees with ours.
        let defSeq = toSeq definer
        let defn = Seq.tryFind (fun (dfunc, _) -> dfunc.Name = func.Name) defSeq
        checkParamCount func defn

    /// <summary>
    ///     Look up <c>func</c> in <c>_arg1</c>, and, if it exists, typecheck
    ///     it against its definition.
    /// </summary>
    /// <param name="func">
    ///     The func to look up in <c>_arg1</c>.
    /// </param>
    /// <param name="definer">
    ///     An associative sequence mapping <c>Func</c>s to some definition.
    /// </param>
    /// <typeparam name="Defn">The type of definer definitions.</typeparam>
    /// <returns>
    ///     A Chessie result, where the <c>ok</c> value is an <c>Option</c>
    ///     containing the pair of
    ///     prototype func and definition, and the failure value is a
    ///     <c>Starling.Core.Definer.Error</c>.  If the <c>ok</c> value is
    ///     <c>None</c>, it means no (valid or otherwise) definition exists.
    /// </returns>
    let lookupWithTypeCheck
      (func : Func<Expr<_>>) (definer : FuncDefiner<'Defn>)
      : Result<(DFunc * 'Defn) option, Error> =
        let unchecked = lookup func definer

        bind
            (function
             | None -> ok None
             | Some (dfunc, defn) ->
                 lift
                     (fun _ -> Some (dfunc, defn))
                     (checkParamTypes func dfunc))
            unchecked


module ViewDefiner =
    /// <summary>
    ///     Converts a <c>ViewDefiner</c> to a sequence of pairs of
    ///     <c>View</c> and definition.
    /// </summary>
    /// <param name="definer">
    ///     A <see cref="ViewDefiner"/> to convert to a sequence.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of <c>View</c> definitions.  May be <c>unit</c>.
    /// </typeparam>
    /// <returns>
    ///     The sequence of (<c>View</c>, <c>'defn</c>) pairs.
    ///     A <c>ViewDefiner</c> allowing the <c>'defn</c>s of the given
    ///     <c>View</c> to be looked up.
    /// </returns>
    let toSeq (definer : ViewDefiner<'defn>) : (DView * 'defn) seq =
        // This function exists to smooth over any changes in Definer
        // representation we make later (eg. to maps).
        List.toSeq definer

    /// <summary>
    ///     Builds a <c>ViewDefiner</c> from a sequence of pairs of
    ///     <c>View</c> and definition.
    /// </summary>
    /// <param name="fseq">
    ///     The sequence of (<c>Func</c>, <c>'defn</c>) pairs.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of <c>Func</c> definitions.  May be <c>unit</c>.
    /// </typeparam>
    /// <returns>
    ///     A <c>ViewDefiner</c> allowing the <c>'defn</c>s of the given
    ///     <c>View</c>s to be looked up.
    /// </returns>
    let ofSeq (fseq : #((DView * 'defn) seq)) : ViewDefiner<'defn> =
        // This function exists to smooth over any changes in Definer
        // representation we make later (eg. to maps).
        Seq.toList fseq


/// <summary>
///     Pretty printers used for definers.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.View.Pretty

    /// Pretty-prints instantiation errors.
    let printError : Error -> Doc =
        function
        | TypeMismatch (par, atype) ->
            fmt "parameter '{0}' conflicts with argument of type '{1}'"
                [ printTypedVar par; printType atype ]
        | CountMismatch (fn, dn) ->
            fmt "view usage has {0} parameter(s), but its definition has {1}"
                [ fn |> sprintf "%d" |> String; dn |> sprintf "%d" |> String ]
