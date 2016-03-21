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
open Starling.Core.Z3

/// <summary>
///     Type for equivalence checks.
/// </summary>
type Equiv = Z3.Context -> Z3.BoolExpr

/// <summary>
///     Runs an equivalence check.
/// </summary>
/// <param name="e">
///     The equivalence check to run.
/// </param>
/// <returns>
///     True if the equivalence check definitely succeeded.
///     False otherwise (including if the check was undecideable).
/// </returns>
let equivHolds (e : Equiv) =
    (* The tactic here is the same as the Starling one:
       negate the equivalence and try to falsify it. *)
    use ctx = new Z3.Context ()
    let term = ctx.MkNot (e ctx)
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
/// <returns>
///     The or-disjunction of the two, which will return true only if
///     (but not necessarily if!) at least one equivalence holds.
/// </returns>
let orEquiv x y : Equiv =
    fun (ctx : Z3.Context) -> ctx.MkOr [| x ctx ; y ctx |]

/// <summary>
///     And-conjoins two equivalence checks.
/// </summary>
/// <param name="x">
///     The first equivalence check to conjoin.
/// </param>
/// <param name="y">
///     The second equivalence check to conjoin.
/// </param>
/// <returns>
///     The and-conjunction of the two, which will return true only if
///     (but not necessarily if!) both equivalences hold.
/// </returns>
let andEquiv x y : Equiv =
    fun (ctx : Z3.Context) -> ctx.MkAnd [| x ctx ; y ctx |]

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
/// <returns>
///     An equivalence check returning true only if (but not if!)
///     <paramref name="x" /> and <paramref name="y" /> are equivalent.
/// </returns>
/// <remarks>
///     This function calls into Z3, and is thus likely to be slow.
///     Use with caution.
/// </remarks>
let equiv x y =
    fun ctx ->
        let sx, sy = (x |> simp |> Expr.boolToZ3 ctx,
                      y |> simp |> Expr.boolToZ3 ctx)
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
/// <returns>
///     An equivalence check returning true only if (but not if!)
///     <paramref name="x" /> and <paramref name="y" /> negate each other.
/// </returns>
/// <remarks>
///     This function calls into Z3, and is thus likely to be slow.
///     Use with caution.
/// </remarks>
let negates x y =
    fun ctx -> equiv x (BNot y) ctx
