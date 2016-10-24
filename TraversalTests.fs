/// <summary>
///     Tests for <c>Sub</c>.
/// </summary>
module Starling.Tests.Core.Traversal

open NUnit.Framework
open Starling.Utils.Testing
open Starling.Core.Expr
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Traversal

open Starling.Core.Pretty
open Starling.Core.Traversal.Pretty

/// <summary>
///     Test cases for finding variables in expressions.
/// </summary>
module FindVars =
    /// <summary>
    ///     Tests finding variables in expressions.
    /// </summary>
    let check (expected : TypedVar list) (expr : Expr<Var>) : unit =
        let result = findVars (tliftOverExpr collectVars) expr
        assertOkAndEqual (Set.ofList expected) result
            (printTraversalError (fun () -> String "?") >> printUnstyled)

    [<Test>]
    let ``Finding vars in a Boolean primitive returns empty`` () =
        check [] (Expr.Bool BTrue)

    [<Test>]
    let ``Finding vars in an integer primitive returns empty`` () =
        check [] (Expr.Int (IInt 1L))

    [<Test>]
    let ``Finding vars in a Boolean var returns that var`` () =
        check [ CTyped.Bool "foo" ] (Expr.Bool (BVar "foo"))

    [<Test>]
    let ``Finding vars in an integer var returns that var`` () =
        check [ CTyped.Int "bar" ] (Expr.Int (IVar "bar"))

    [<Test>]
    let ``Finding vars in a Boolean expression works correctly`` () =
        check
            [ CTyped.Bool "foo"
              CTyped.Bool "baz"
              CTyped.Int "foobar"
              CTyped.Int "barbaz" ]
            (Expr.Bool
                (BAnd
                    [ BOr [ BVar "foo"; BVar "baz" ]
                      BGt ( IVar "foobar", IVar "barbaz" ) ] ))

    [<Test>]
    let ``Finding vars in an integer expression works correctly`` () =
        check
            [ CTyped.Int "foo"
              CTyped.Int "bar"
              CTyped.Int "foobar"
              CTyped.Int "barbaz" ]
            (Expr.Int
                (IAdd
                    [ ISub [ IVar "foo"; IVar "bar" ]
                      IMul [ IVar "foobar"; IVar "barbaz" ]] ))
