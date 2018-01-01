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
        check [] (normalBoolExpr BTrue)

    [<Test>]
    let ``Finding vars in an integer primitive returns empty`` () =
        check [] (normalIntExpr (IInt 1L))

    [<Test>]
    let ``Finding vars in a Boolean var returns that var`` () =
        check [ normalBoolVar "foo" ] (normalBoolExpr (BVar "foo"))

    [<Test>]
    let ``Finding vars in an integer var returns that var`` () =
        check [ normalIntVar "bar" ] (normalIntExpr (IVar "bar"))

    [<Test>]
    let ``Finding vars in a Boolean expression works correctly`` () =
        check
            [ normalBoolVar "foo"
              normalBoolVar "baz"
              normalIntVar "foobar"
              normalIntVar "barbaz" ]
            (normalBoolExpr
                (BAnd
                    [ BOr [ BVar "foo"; BVar "baz" ]
                      BGt ( normalInt (IVar "foobar"), normalInt (IVar "barbaz")) ] ))

    [<Test>]
    let ``Finding vars in an integer expression works correctly`` () =
        check
            [ normalIntVar "foo"
              normalIntVar "bar"
              normalIntVar "foobar"
              normalIntVar "barbaz" ]
            (normalIntExpr
                (IAdd
                    [ ISub [ IVar "foo"; IVar "bar" ]
                      IMul [ IVar "foobar"; IVar "barbaz" ]] ))
