/// <summary>
///     Tests for <c>Sub</c>.
/// </summary>
module Starling.Tests.Core.Sub

open NUnit.Framework
open Starling.Utils.Testing
open Starling.Core.Expr
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Sub

open Starling.Core.Pretty
open Starling.Core.Sub.Pretty

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
            (printSubError (fun () -> String "?") >> printUnstyled)

    [<Test>]
    let ``Finding vars in a Boolean primitive returns empty`` () =
        check [] (Expr.Bool BTrue)

    [<Test>]
    let ``Finding vars in an integer primitive returns empty`` () =
        check [] (Expr.Int (AInt 1L))

    [<Test>]
    let ``Finding vars in a Boolean var returns that var`` () =
        check [ CTyped.Bool "foo" ] (Expr.Bool (BVar "foo"))

    [<Test>]
    let ``Finding vars in an integer var returns that var`` () =
        check [ CTyped.Int "bar" ] (Expr.Int (AVar "bar"))

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
                      BGt ( AVar "foobar", AVar "barbaz" ) ] ))

    [<Test>]
    let ``Finding vars in an integer expression works correctly`` () =
        check
            [ CTyped.Int "foo"
              CTyped.Int "bar"
              CTyped.Int "foobar"
              CTyped.Int "barbaz" ]
            (Expr.Int
                (AAdd
                    [ ASub [ AVar "foo"; AVar "bar" ]
                      AMul [ AVar "foobar"; AVar "barbaz" ]] ))
