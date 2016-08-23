/// <summary>
///     Parser tests.
/// </summary>
module Starling.Tests.Lang.Parser

open NUnit.Framework

open Starling
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.View
open Starling.Lang.AST
open Starling.Lang.Parser

open FParsec

let get =
    function
    | Success(r, _, _) -> Some r
    | Failure _ -> None

let check p str ast = 
    let actual = run p str 
    Assert.AreEqual (ast, get actual)


// Perform the same trick matt uses in Main.fs to overwrite a right-associative
// operator with the correct behaviour
let ( ** ) = ( <| )


// Conversion of mattw's test cases into new system
module ExpressionTests = 
    [<Test>]
    let ``Test order-of-operations on (1 + 2 * 3)``() =
        check parseExpression "1 + 2 * 3" <| Some
        ** node "" 1L 3L 
            ** BopExpr (Add, 
                    node "" 1L 1L (Num 1L),
                    node "" 1L 7L 
                        <| BopExpr (Mul,
                                node "" 1L 5L (Num 2L),
                                node "" 1L 9L (Num 3L)))
    [<Test>]
    let ``Test bracketing on (1 + 2) * 3``() =
        check parseExpression "(1 + 2) * 3"  <| Some
        ** node "" 1L 9L
            ** BopExpr (Mul,
                    node "" 1L 4L
                    <| BopExpr (Add,
                            node "" 1L 2L (Num 1L),
                            node "" 1L 6L (Num 2L)),
                    node "" 1L 11L (Num 3L))

    [<Test>]
    let ``Complex expression 1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8``() =
        check parseExpression "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8"  <| Some
        ** node "" 1L 23L
            ** BopExpr (Or,
                    node "" 1L 15L
                    <| BopExpr (And,
                            node "" 1L 7L
                            <| BopExpr (Lt,
                                    node "" 1L 3L
                                    <| BopExpr (Add,
                                            node "" 1L 1L (Num 1L),
                                            node "" 1L 5L (Num 2L)),
                                    node "" 1L 11L
                                    <| BopExpr (Mul,
                                            node "" 1L 9L (Num 3L),
                                            node "" 1L 13L (Num 4L))),
                            node "" 1L 18L True),
                    node "" 1L 32L
                    <| BopExpr (Gt,
                            node "" 1L 28L
                            <| BopExpr (Div,
                                    node "" 1L 26L (Num 5L),
                                    node "" 1L 30L (Num 6L)),
                            node "" 1L 36L
                            <| BopExpr (Sub,
                                    node "" 1L 34L (Num 7L),
                                    node "" 1L 38L (Num 8L))))
module AtomicActionTests =
    [<Test>]
    let ``foo++``() =
        check parseAtomic "foo++" <| Some ** node "" 1L 1L (Postfix(LVIdent "foo", Increment))

    [<Test>]
    let ``foo--`` =
        check parseAtomic "foo--" <| Some ** node "" 1L 1L (Postfix(LVIdent "foo", Decrement))

    [<Test>]
    let ``foo = bar`` =
        check parseAtomic "foo = bar"  <| Some
        ** node "" 1L 1L (Fetch(LVIdent "foo", node "" 1L 7L <| LV(LVIdent "bar"), Direct))

    [<Test>]
    let ``foo = bar++`` =
        check parseAtomic "foo = bar++" <| Some
        ** node "" 1L 1L (Fetch(LVIdent "foo", node "" 1L 7L <| LV(LVIdent "bar"), Increment))

    [<Test>]
    let ``foo = bar--`` =
        check parseAtomic "foo = bar--" <| Some
        ** node "" 1L 1L (Fetch(LVIdent "foo", node "" 1L 7L <| LV(LVIdent "bar"), Decrement))

    [<Test>]
    let ``Compare and swap``() =
        check parseAtomic "CAS(foo, bar, 2)" <| Some
        ** node "" 1L 1L 
           (CompareAndSwap( LVIdent "foo", 
                            LVIdent "bar", 
                            node "" 1L 15L (Num 2L)))

module AtomicSetTests =
    [<Test>]
    let ``<foo++>``() =
        check parseAtomicSet "<foo++>"
        <| Some ** [
            node "" 1L 2L (Postfix (LVIdent "foo", Increment))
            ]

    [<Test>]
    let ``Multiple outside block invalid``() =
        check parseAtomicSet "<foo++; bar-->" None

    [<Test>]
    let ``Single atomic block``() =
        check parseAtomicSet "<{ foo++; }>"
        <| Some [
            node "" 1L 4L (Postfix (LVIdent "foo", Increment))
            ]

    [<Test>]
    let ``Multiple in block valid``() =
        check parseAtomicSet "<{ foo++; bar--; }>"
        <| Some [
            node "" 1L 4L (Postfix (LVIdent "foo", Increment))
            node "" 1L 11L (Postfix (LVIdent "bar", Decrement))
            ]

module ConstraintTests =
    [<Test>]
    let ``emp -> true``() =
        check parseConstraint "constraint emp -> true;"
        <| Some (DView.Unit, Some <| node "" 1L 19L True)

    [<Test>]
    let ``Func(a,b) -> c > a + b``() =
        check parseConstraint "constraint Func(a, b) -> c > a + b;"
        <| Some (DView.Func { Name = "Func"
                              Params = [ "a"; "b" ] },
                 Some
                   (node "" 1L 28L
                    <| BopExpr (Gt,
                                node "" 1L 26L (LV(LVIdent "c")),
                                node "" 1L 32L
                                <| BopExpr(Add,
                                       node "" 1L 30L (LV(LVIdent "a")),
                                       node "" 1L 34L (LV(LVIdent "b"))))))

    [<Test>]
    let ``Func(a,b) -> ?;``() =
        check parseConstraint "constraint Func(a, b) -> ?;"
        <| Some (DView.Func { Name = "Func"
                              Params = [ "a"; "b" ] },
                 (None : Expression option))
