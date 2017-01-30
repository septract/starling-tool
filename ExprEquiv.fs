/// <summary>
///     Heavyweight expression equivalence checks.
///
///     <para>
///         Unlike normal expression checks, these produce <c>Equiv</c>
///         values, which must be passed to <c>runEquiv</c> to check.
///     </para>
///
///     <para>
///         These are farmed out to Z3.  As such, they are not likely to
///         execute quickly.  Use with caution.
///     </para>
/// </summary>
module Starling.Core.ExprEquiv

open Microsoft
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Z3


/// <summary>
///     Type for equivalence checks.
/// </summary>
type Equiv<'var> = ('var -> string) -> Z3.Context -> Z3.BoolExpr

/// <summary>
///     Runs an equivalence check.
/// </summary>
/// <param name="toVar">
///     A function converting variables in the check to <c>Var</c>s.
///     The vars must be unique to their origin variables across the
///     equivalence.
/// </param>
/// <param name="e">
///     The equivalence check to run.
/// </param>
/// <typeparam name="var">
///     Meta-type of variables inside the equivalence-checked expressions.
/// </typeparam>
/// <returns>
///     True if the equivalence check definitely succeeded.
///     False otherwise (including if the check was undecideable).
/// </returns>
let equivHolds
  (toVar : 'var -> Var)
  (e : Equiv<'var>) =
    (* The tactic here is the same as the Starling one:
       negate the equivalence and try to falsify it. *)
    use ctx = new Z3.Context ()
    let term = ctx.MkNot (e toVar ctx)
    match (Run.runTerm ctx term) with
    | Z3.Status.UNSATISFIABLE -> true
    | _ -> false

/// <summary>
///     Or-disjoins two equivalence checks.
/// </summary>
/// <param name="x">
///     The first equivalence check to disjoin.
/// </param>
/// <param name="y">
///     The second equivalence check to disjoin.
/// </param>
/// <typeparam name="var">
///     Meta-type of variables inside the equivalence-checked expressions.
/// </typeparam>
/// <returns>
///     The or-disjunction of the two, which will return true only if
///     (but not necessarily if!) at least one equivalence holds.
/// </returns>
let orEquiv (x : Equiv<'var>) (y : Equiv<'var>) : Equiv<'var> =
    fun toVar (ctx : Z3.Context) ->
        ctx.MkOr [| x toVar ctx ; y toVar ctx |]

/// <summary>
///     And-conjoins two equivalence checks.
/// </summary>
/// <param name="x">
///     The first equivalence check to conjoin.
/// </param>
/// <param name="y">
///     The second equivalence check to conjoin.
/// </param>
/// <typeparam name="var">
///     Meta-type of variables inside the equivalence-checked expressions.
/// </typeparam>
/// <returns>
///     The and-conjunction of the two, which will return true only if
///     (but not necessarily if!) both equivalences hold.
/// </returns>
let andEquiv (x : Equiv<'var>) (y : Equiv<'var>) : Equiv<'var> =
    fun toVar (ctx : Z3.Context) ->
        ctx.MkAnd [| x toVar ctx ; y toVar ctx |]

/// <summary>
///     Returns true if two expressions are definitely equivalent to each
///     other.
///
///     <para>
///         This is sound, but not complete.  It should only be used for
///         optimisations.
///     </para>
/// </summary>
/// <param name="x">
///     The first expression to check.
/// </param>
/// <param name="y">
///     The second expression to check.
/// </param>
/// <typeparam name="var">
///     Meta-type of variables inside the equivalence-checked expressions.
/// </typeparam>
/// <returns>
///     An equivalence check returning true only if (but not if!)
///     <paramref name="x" /> and <paramref name="y" /> are equivalent.
/// </returns>
/// <remarks>
///     This function calls into Z3, and is thus likely to be slow.
///     Use with caution.
/// </remarks>
let equiv (x : BoolExpr<'var>) (y : BoolExpr<'var>) : Equiv<'var> =
    fun toVar ctx ->
        let sx = Expr.boolToZ3 false toVar ctx (normalBool (simp x))
        let sy = Expr.boolToZ3 false toVar ctx (normalBool (simp y))
        ctx.MkIff (sx, sy)

/// <summary>
///     Returns true if two expressions are definitely negations of each
///     other.
///
///     <para>
///         This is sound, but not complete.  It should only be used for
///         optimisations.
///     </para>
/// </summary>
/// <param name="x">
///     The first expression to check.
/// </param>
/// <param name="y">
///     The second expression to check.
/// </param>
/// <typeparam name="var">
///     Meta-type of variables inside the equivalence-checked expressions.
/// </typeparam>
/// <returns>
///     An equivalence check returning true only if (but not if!)
///     <paramref name="x" /> and <paramref name="y" /> negate each other.
/// </returns>
/// <remarks>
///     This function calls into Z3, and is thus likely to be slow.
///     Use with caution.
/// </remarks>
let negates (x : BoolExpr<'var>) (y : BoolExpr<'var>) : Equiv<'var> =
    fun toVar ctx -> equiv x (BNot y) toVar ctx


/// <summary>
///     Tests for <c>ExprEquiv</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Starling.Utils.Testing
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty

    /// <summary>
    ///     NUnit tests for <c>ExprEquiv</c>.
    /// </summary>
    type NUnit () =
        /// Test cases for negation checking.
        static member ObviousNegations =
            [ (tcd [| (BTrue : VBoolExpr)
                      (BFalse : VBoolExpr) |])
                .Returns(true)
              (tcd [| (BTrue : VBoolExpr)
                      (BTrue : VBoolExpr) |])
                .Returns(false)
              (tcd [| (BFalse : VBoolExpr)
                      (BFalse : VBoolExpr) |])
                .Returns(false)
              (tcd [| (BTrue : VBoolExpr)
                      (iEq (IInt 5L) (IInt 6L) : VBoolExpr) |])
                .Returns(true)
              (tcd [| (iEq (IVar "x") (IInt 2L))
                      (BNot (iEq (IVar "x") (IInt 2L))) |])
                .Returns(true)
              (tcd [| (iEq (IVar "x") (IInt 2L))
                      (BNot (iEq (IVar "y") (IInt 2L))) |])
                .Returns(false)
              // De Morgan
              (tcd [| (BAnd [ BVar "x" ; BVar "y" ])
                      (BOr [ BNot (BVar "x")
                             BNot (BVar "y") ] ) |] )
                .Returns(true)
              (tcd [| (BAnd [ BVar "x" ; BVar "y" ])
                      (BOr [ BNot (BVar "y")
                             BNot (BVar "x") ] ) |] )
                .Returns(true)
              (tcd [| (BOr [ BVar "x" ; BVar "y" ])
                      (BAnd [ BNot (BVar "x")
                              BNot (BVar "y") ] ) |] )
                .Returns(true)
              (tcd [| (BOr [ BVar "x" ; BVar "y" ])
                      (BAnd [ BNot (BVar "y")
                              BNot (BVar "x") ] ) |] )
                .Returns(true) ]
            |> List.map (
                fun d -> d.SetName(sprintf "%s and %s are %s negation"
                                            (((d.OriginalArguments.[1])
                                              :?> VBoolExpr)
                                             |> printVBoolExpr |> print)
                                            (((d.OriginalArguments.[0])
                                              :?> VBoolExpr)
                                             |> printVBoolExpr |> print)
                                            (if (d.ExpectedResult :?> bool)
                                             then "a" else "not a")))

        /// Checks whether negation checking is sound and sufficiently complete.
        [<TestCaseSource("ObviousNegations")>]
        member x.``negates is sound and sufficiently complete`` a b =
            equivHolds id (negates a b)
