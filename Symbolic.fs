/// <summary>
///     Symbolic variables, and functions for dealing with them.
///
///     <para>
///         Symbolic variables (<c>Sym</c>) are how Starling encodes
///         arbitrary functions on zero or more variables that involve
///         syntax or concepts Starling can't internally handle.
///     </para>
///     <para>
///         They overload the variable position in expressions with a
///         disjunction between regular variables and uninterpreted,
///         arbitrary strings.  These strings are parameterised by
///         expression variables, as if they were method calls.
///         However, they represent a textual substitution of the
///         given variables into the string.
///     </para>
///     <para>
///         Starling proofs using symbolic variables cannot be proven
///         automatically.  Instead, the symbols must either be removed,
///         or replaced with some other Starling construct.  The typemap
///         <c>tryRemoveSym</c> tries to remove all <c>Sym</c>s from
///         expressions, failing if any exist.  The function
///         <c>approx</c> substitutes <c>true</c> and <c>false</c> for
///         symbols in Boolean positions, depending on whether they arise
///         in a positive or negative position.
///     </para>
/// </summary>
module Starling.Core.Symbolic

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Traversal

/// <summary>
///     Types for symbolic and variable maps.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A variable reference that may be symbolic.
    ///
    ///     <para>
    ///         A symbolic variable is one whose value depends on an
    ///         uninterpreted function of multiple 'real' Starling variables.
    ///         It allows encoding into Starling of patterns of variable usage
    ///         Starling doesn't yet understand natively.
    ///     </para>
    /// </summary>
    /// <typeparam name="var">
    ///     The non-symbolic variable <c>Sym</c> wraps.
    /// </typeparam>
    type Sym<'var> when 'var : equality =
        /// <summary>
        ///     A symbolic variable, predicated over multiple expressions.
        ///     The symbol itself is the name inside the <c>Func</c>.
        /// </summary>
        | Sym of Func<Expr<Sym<'var>>>
        /// <summary>
        ///     A regular, non-symbolic variable.
        | Reg of 'var


/// <summary>
///     Type synonyms for expressions over various forms of symbolic
///     variable.
/// </summary>
[<AutoOpen>]
module SymExprs =
    /// <summary>
    ///     An expression of arbitrary type using symbolic <c>Var</c>s.
    /// </summary>
    type SVExpr = Expr<Sym<Var>>
    /// <summary>
    ///     An expression of Boolean type using symbolic <c>Var</c>s.
    /// </summary>
    type SVBoolExpr = BoolExpr<Sym<Var>>
    /// <summary>
    ///     An expression of integral type using <c>Var</c>s.
    /// </summary>
    type SVIntExpr = IntExpr<Sym<Var>>

    /// <summary>
    ///     An expression of arbitrary type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMExpr = Expr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of Boolean type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMBoolExpr = BoolExpr<Sym<MarkedVar>>
    /// <summary>
    ///     An expression of integral type using symbolic <c>MarkedVar</c>s.
    /// </summary>
    type SMIntExpr = IntExpr<Sym<MarkedVar>>


/// <summary>
///     Utilities for creating symbolic variables.
/// </summary>
[<AutoOpen>]
module Create =
    /// Creates a symbolic variable given its body and parameters.
    let sym (body : string) (xs : Expr<Sym<'Var>> list) : Sym<'Var> =
        Sym { Name = body; Params = xs }

    /// Creates an integer sym-variable.
    let siVar c = c |> Reg |> IVar

    /// Creates an before-marked integer sym-variable.
    let siBefore c = c |> Before |> Reg |> IVar

    /// Creates an after-marked integer sym-variable.
    let siAfter c = c |> After |> Reg |> IVar

    /// Creates a goal-marked integer sym-variable.
    let siGoal i c = (i, c) |> Goal |> Reg |> IVar

    /// Creates an intermediate-marked integer sym-variable.
    let siInter i c = (i, c) |> Intermediate |> Reg |> IVar

    /// Creates a Boolean sym-variable.
    let sbVar c = c |> Reg |> BVar

    /// Creates an before-marked Boolean sym-variable.
    let sbBefore c = c |> Before |> Reg |> BVar

    /// Creates an before-marked Boolean sym-variable.
    let sbAfter c = c |> After |> Reg |> BVar

    /// Creates a goal-marked Boolean sym-variable.
    let sbGoal i c = (i, c) |> Goal |> Reg |> BVar

    /// Creates an intermediate-marked Boolean sym-variable.
    let sbInter i c = (i, c) |> Intermediate |> Reg |> BVar


/// <summary>
///     Utilities to traverse or eliminate symbolic variables.
/// </summary>
module Traversal =
    /// <summary>
    ///     Lifts a Traversal from variables to symbolic variables to accept
    ///     symbolic variables.
    /// </summary>
    let rec tliftToSymSrc
      (sub : Traversal<'SrcVar, Sym<'DstVar>, 'Error>)
      : Traversal<Sym<'SrcVar>, Sym<'DstVar>, 'Error> =
        fun ctx ->
            function
            | Reg r -> sub ctx r
            | Sym { Name = body; Params = rs } ->
                // TODO(CaptainHayashi): this is horrible.
                // Are our abstractions wrong?
                tchainL
                    (sub
                     |> tliftToSymSrc
                     |> tliftOverCTyped
                     |> tliftOverExpr)
                    (sym body)
                    ctx rs

    /// <summary>
    ///     Lifts a Traversal from variables to variables to return
    ///     symbolic variables.
    /// </summary>
    let tliftToSymDest
      (sub : Traversal<'SrcVar, 'DstVar, 'Error>)
      : Traversal<'SrcVar, Sym<'DstVar>, 'Error> =
        fun ctx -> sub ctx >> lift (pairMap id Reg)

    /// <summary>
    ///     Lifts a Traversal from variables to variables to one from
    ///     symbolic variables to symbolic variables.
    /// </summary>
    let tliftOverSym
      (sub : Traversal<'SrcVar, 'DstVar, 'Error>)
      : Traversal<Sym<'SrcVar>, Sym<'DstVar>, 'Error> =
        sub |> tliftToSymDest |> tliftToSymSrc

    /// <summary>
    ///     A traversal for removing symbols from variables.
    /// </summary>
    /// <param name="err">
    ///     Function mapping a symbol's contents to an error to throw when
    ///     detecting one.
    /// </param>
    /// <typeparam name="Error">
    ///     The type of <paramref name="err"/>.
    /// </typeparam>
    /// <typeparam name="Var">
    ///     The type of regular (non-symbolic) variables.
    /// </typeparam>
    /// <returns>
    ///     A <see cref="Traversal"/> trying to remove symbols from
    ///     variables.
    /// </returns>
    let removeSymFromVar (err : string -> 'Error)
      : Traversal<Sym<'Var>, 'Var, 'Error> =
        ignoreContext
            (function
             | Sym s -> s.Name |> err |> Inner |> fail
             | Reg f -> ok f)

    /// <summary>
    ///     A traversal for removing symbols from expressions.
    /// </summary>
    /// <param name="err">
    ///     Function mapping a symbol's contents to an error to throw when
    ///     detecting one.
    /// </param>
    /// <typeparam name="Error">The type of <paramref name="err"/>.</typeparam>
    /// <typeparam name="Var">
    ///     The type of regular (non-symbolic) variables.
    /// </typeparam>
    /// <returns>
    ///     A <see cref="Traversal"/> trying to remove symbols from
    ///     expressions.
    /// </returns>
    let removeSymFromExpr (err : string -> 'Error)
      : Traversal<Expr<Sym<'Var>>, Expr<'Var>, 'Error> =
        (tliftOverExpr (tliftOverCTyped (removeSymFromVar err)))

    /// <summary>
    ///     A traversal for removing symbols from Boolean expressions.
    /// </summary>
    /// <param name="err">
    ///     Function mapping a symbol's contents to an error to throw when
    ///     detecting one.
    /// </param>
    /// <typeparam name="Error">The type of <paramref name="err"/>.</typeparam>
    /// <typeparam name="Var">
    ///     The type of regular (non-symbolic) variables.
    /// </typeparam>
    /// <returns>
    ///     A <see cref="Traversal"/> trying to remove symbols from
    ///     Boolean expressions.
    /// </returns>
    let removeSymFromBoolExpr (err : string -> 'Error)
      : Traversal<BoolExpr<Sym<'Var>>, BoolExpr<'Var>, 'Error> =
        tliftToBoolSrc
            (tliftToExprDest
                (tliftOverCTyped (removeSymFromVar err)))

    (*
     * Common traversals
     *)

    /// <summary>
    ///     Lifts a traversal from typed variables to symbolic expressions
    ///     such that it now takes typed symbolic variables as input.
    ///     <para>
    ///         This is needed because <see cref="tliftToExprSrc"/>
    ///         and other such traversals don't play well with symbolics.
    ///     </para>
    /// </summary>
    /// <param name="traversal">The <see cref="Traversal"/> to lift.</param>
    /// <typeparam name="SrcVar">Type of variables entering traversal.</param>
    /// <typeparam name="DstVar">Type of variables leaving traversal.</param>
    /// <returns>The lifted <see cref="Traversal"/>.</returns>
    let rec tliftToTypedSymVarSrc
      (traversal : Traversal<CTyped<'SrcVar>, Expr<Sym<'DstVar>>, 'Error>)
      : Traversal<CTyped<Sym<'SrcVar>>, Expr<Sym<'DstVar>>, 'Error> =
        let rec subInTypedSym ctx sym =
            match (valueOf sym) with
            | Reg r -> traversal ctx (withType (typeOf sym) r)
            | Sym { Name = n; Params = ps } ->
                tchainL sub
                    (fun ps' ->
                        mkVarExp
                            (withType (typeOf sym)
                                (Sym { Name = n; Params = ps' })))
                    ctx ps
        and sub = tliftToExprSrc subInTypedSym
        subInTypedSym

    /// <summary>
    ///     Traversal for converting symbolic expressions with a marker.
    /// </summary>
    let traverseSymWithMarker
      (marker : Var -> MarkedVar)
      : Traversal<Sym<Var>, Sym<MarkedVar>, 'Error> =
        tliftOverSym (ignoreContext (marker >> ok))

    /// <summary>
    ///     Traversal for converting type-annotated symbolic variables with a
    ///     marker.
    /// </summary>
    /// <param name="marker">The marker to lift into a traversal.</param>
    /// <returns>
    ///     The marker function <paramref name="marker"/>, lifted into a
    ///     <see cref="Traversal"/> over symbolic <see cref="Var"/>s annotated
    ///     using <see cref="CTyped"/>.
    /// </returns>
    let traverseTypedSymWithMarker
      (marker : Var -> MarkedVar)
      : Traversal<CTyped<Sym<Var>>, CTyped<Sym<MarkedVar>>, 'Error> =
        tliftOverCTyped (traverseSymWithMarker marker)

    /// <summary>
    ///     Converts a symbolic expression to its pre-state.
    /// </summary>
    let before (expr : Expr<Sym<Var>>)
      : Result<Expr<Sym<MarkedVar>>, TraversalError<'Error>> =
        mapTraversal (tliftOverExpr (traverseTypedSymWithMarker Before)) expr

    /// <summary>
    ///     Converts a symbolic expression to its post-state.
    /// </summary>
    let after (expr : Expr<Sym<Var>>)
      : Result<Expr<Sym<MarkedVar>>, TraversalError<unit>> =
        mapTraversal (tliftOverExpr (traverseTypedSymWithMarker After)) expr

    /// <summary>
    ///     Replaces symbols in a Boolean position with their
    ///     under-approximation.
    /// </summary>
    let approx
      : Traversal<CTyped<Sym<MarkedVar>>, Expr<Sym<MarkedVar>>, unit> =
        let rec sub ctx =
            // Only symbolic Booleans are handled specially.
            function
            | Bool (Sym x) ->
                match ctx with
                | Positions (position::_) ->
                    ok (ctx, position |> Context.underapprox |> Bool)
                | c -> fail (ContextMismatch ("position context", c))
            (* Everything else just has approximation bubbled through
               in a type-generic way. *)
            | WithType (Sym { Name = body; Params = rs }, t) ->
                tchainL rmap (sym body >> withType t >> mkVarExp) ctx rs
            | WithType (Reg x, t) ->
                ok (ctx, mkVarExp (withType t (Reg x)))
        and sf = tliftToExprSrc sub
        and rmap ctx = sf (Context.push id ctx)

        sub

/// <summary>
///     Traversal for accumulating symbolic <c>MarkedVar</c>s.
/// <summary>
let rec collectSymVars
  : Traversal<CTyped<Sym<Var>>, CTyped<Sym<Var>>, 'Error> =
    // TODO(CaptainHayashi): de-duplicate this.
    fun ctx ->
        function
        | WithType (Reg v, tc) ->
            lift
                (fun ctx -> (ctx, withType tc (Reg v)))
                (pushVar ctx (withType tc v))
        | WithType (Sym { Name = body; Params = ps }, tc) ->
            tchainL
                (tliftOverExpr collectSymVars)
                (sym body >> withType tc)
                ctx ps

/// <summary>
///     Traversal for accumulating symbolic <c>MarkedVar</c>s.
/// <summary>
let rec collectSymMarkedVars
  : Traversal<CTyped<Sym<MarkedVar>>, CTyped<Sym<MarkedVar>>, 'Error> =
    // TODO(CaptainHayashi): de-duplicate this.
    fun ctx ->
        function
        | WithType (Reg v, tc) ->
            lift
                (fun ctx -> (ctx, withType tc (Reg v)))
                (pushMarkedVar ctx (withType tc v))
        | WithType (Sym { Name = body; Params = ps }, tc) ->
            tchainL
                (tliftOverExpr collectSymMarkedVars)
                (sym body >> withType tc)
                ctx ps

/// <summary>
///     Pretty printers for symbolics.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Var.Pretty

    /// <summary>
    ///     Pretty-prints a <c>Sym</c>.
    /// </summary>
    /// <param name="pReg">
    ///     Pretty printer to use for regular variables.
    /// </param>
    /// <returns>
    ///     A function taking <c>Sym</c>s and returning pretty-printer
    ///     <c>Command</c>s.
    /// </returns>
    let rec printSym pReg =
        function
        | Sym { Name = sym ; Params = regs } ->
            func (sprintf "%%{%s}" sym) (Seq.map (printExpr (printSym pReg)) regs)
        | Reg reg -> pReg reg

    /// Pretty-prints a SVExpr.
    let printSVExpr = printExpr (printSym String)
    /// Pretty-prints a SMExpr.
    let printSMExpr = printExpr (printSym printMarkedVar)
    /// Pretty-prints a SVBoolExpr.
    let printSVBoolExpr = printBoolExpr (printSym String)
    /// Pretty-prints a SMBoolExpr.
    let printSMBoolExpr = printBoolExpr (printSym printMarkedVar)

/// Strip the marked part of the annotation
/// and return just the internal 'var
let unmarkMarkedVar =
    function
    | Before s            -> s
    | After s             -> s
    | Goal(_, s)          -> s
    | Intermediate(_, s)  -> s

/// Takes a type annotated MarkedVar and strips away the Marked part of the Var
/// i.e. (Int (Before s)) => (Int s)
let unmark : CTyped<MarkedVar> -> TypedVar = mapCTyped unmarkMarkedVar

let markedSymExprVars (expr : Expr<Sym<MarkedVar>>)
  : Result<Set<CTyped<MarkedVar>>, TraversalError<'Error>> =
    findMarkedVars (tliftOverExpr collectSymMarkedVars) expr

/// Returns the set of all variables annotated with their types
/// contained within the SMExpr
let SMExprVars : SMExpr -> Result<Set<TypedVar>, TraversalError<'Error>> =
    fun expr ->
        let smvars = markedSymExprVars expr
        lift (Set.map unmark) smvars
