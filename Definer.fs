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
    ///     Merges two definers.
    /// </summary>
    /// <param name="x">The first <see cref="FuncDefiner"/> to merge.</param>
    /// <param name="y">The second <see cref="FuncDefiner"/> to merge.</param>
    /// <typeparam name="Defn">
    ///     The type of <c>Func</c> definitions.  May be <c>unit</c>.
    /// </typeparam>
    /// <returns>
    ///     The <see cref="FuncDefiner"/> containing definitions from both
    ///     <paramref name="x"/> and <paramref name="y"/>.
    /// </returns>
    /// <remarks>
    ///    This does not yet check for duplicates.
    /// </remarks>
    let combine
      (x : FuncDefiner<'Defn>) (y : FuncDefiner<'Defn>) : FuncDefiner<'Defn> =
        // TODO(CaptainHayashi): duplicate checking.
        let xs = toSeq x
        let ys = toSeq y
        let xys = Seq.append x y
        ofSeq xys

    /// <summary>
    ///     Checks whether <c>func</c> and <c>_arg1</c> agree on parameter
    ///     count.
    /// </summary>
    /// <param name="func">
    ///     The func being looked up, the process of which this check is part.
    /// </param>
    /// <param name="defn">
    ///     An <c>Option</c>al pair of <c>DFunc</c> and its defining
    ///     <c>BoolExpr</c>.
    ///     The value <c>None</c> suggests that <c>func</c> has no definition,
    ///     which can be ok (eg. if the <c>func</c> is a non-defining view).
    /// </param>
    /// <typeparam name="Par">The type of func-signature parameters.</typeparam>
    /// <typeparam name="Arg">The type of func arguments.</typeparam>
    /// <typeparam name="Defn">The type of func definitions.</typeparam>
    /// <returns>
    ///     A Chessie result, where the <c>ok</c> value is the optional pair of
    ///     prototype func and definition, and the failure value is a
    ///     <c>Starling.Core.Definer.Error</c>.
    /// </returns>
    let checkParamCount (func : Func<'Arg>) (defn : (Func<'Par> * 'Defn) option)
       : Result<(Func<'Par> * 'Defn) option, Error> =
        match defn with
        | None -> ok None
        | Some def ->
            let fn = List.length func.Params
            let dn = List.length (fst def).Params
            if fn = dn then ok (Some def) else CountMismatch (fn, dn) |> fail

    /// <summary>
    ///     Checks whether <c>func</c> and <c>defn</c> agree on parameter
    ///     types.
    /// </summary>
    /// <param name="func">
    ///     The func being looked up, the process of which this check is part.
    /// </param>
    /// <param name="defn">
    ///     The <c>DFunc</c> that <paramref name="func" /> has matched.
    /// </param>
    /// <typeparam name="Var">
    ///     The type of variables in <paramref name="func"/>.
    /// </typeparam>
    /// <returns>
    ///     A Chessie result, where the <c>ok</c> value is
    ///     <paramref name="func" />, and the failure value is a
    ///     <c>Starling.Core.Definer.Error</c>.
    /// </returns>
    let checkParamTypes (func : Func<Expr<'Var>>) (defn : Func<TypedVar>)
       : Result<Func<Expr<'Var>>, Error> =
        List.map2
            (fun fp dp ->
                if typesCompatible (typeOf fp) (typeOf dp)
                then ok ()
                else fail (TypeMismatch (dp, typeOf fp)))
            func.Params
            defn.Params
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
    let printError (err : Error) : Doc =
        match err with
        | TypeMismatch (par, atype) ->
            errorStr "parameter"
            <+> quoted (printTypedVar par)
            <+> errorStr "conflicts with argument of type"
            <+> quoted (printType atype)
        | CountMismatch (fn, dn) ->
            errorStr "view usage has"
            <+> errorStr (sprintf "%d" fn)
            <+> errorStr "arguments, but its definition has"
            <+> errorStr (sprintf "%d" dn)
