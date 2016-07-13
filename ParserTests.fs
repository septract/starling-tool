/// <summary>
///     Parser tests.
/// </summary>
module Starling.Tests.Lang.Parser

open NUnit.Framework

open Starling
open Starling.Core.Var
open Starling.Core.Model
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
        **  {Position = {StreamName = ""; Line = 1L; Column = 3L}
             Node =
              Bop (Add, 
                   {Position = {StreamName = ""; Line = 1L; Column = 1L}
                    Node = Int 1L},
                   {Position = {StreamName = ""; Line = 1L; Column = 7L}
                    Node = Bop (Mul,
                                {Position = {StreamName = ""; Line = 1L; Column = 5L}
                                 Node = Int 2L
                                },
                                {Position = {StreamName = ""; Line = 1L; Column = 9L}
                                 Node = Int 3L})
                                }
                  )
            }

    [<Test>]
    let ``Test bracketing on (1 + 2) * 3``() =
        check parseExpression "(1 + 2) * 3"  <| Some
        ** node "" 1L 9L
            ** Bop (Mul,
                    node "" 1L 4L
                    <| Bop (Add,
                            node "" 1L 2L (Int 1L),
                            node "" 1L 6L (Int 2L)),
                    node "" 1L 11L (Int 3L))

    [<Test>]
    let ``Complex expression 1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8``() =
        check parseExpression "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8"  <| Some
        ** node "" 1L 23L
            ** Bop (Or,
                    node "" 1L 15L
                    <| Bop (And,
                            node "" 1L 7L
                            <| Bop (Lt,
                                    node "" 1L 3L
                                    <| Bop (Add,
                                            node "" 1L 1L (Int 1L),
                                            node "" 1L 5L (Int 2L)),
                                    node "" 1L 11L
                                    <| Bop (Mul,
                                            node "" 1L 9L (Int 3L),
                                            node "" 1L 13L (Int 4L))),
                            node "" 1L 18L True),
                    node "" 1L 32L
                    <| Bop (Gt,
                            node "" 1L 28L
                            <| Bop (Div,
                                    node "" 1L 26L (Int 5L),
                                    node "" 1L 30L (Int 6L)),
                            node "" 1L 36L
                            <| Bop (Sub,
                                    node "" 1L 34L (Int 7L),
                                    node "" 1L 38L (Int 8L))))
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
                            node "" 1L 15L (Int 2L)))

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
        <| Some (Definite (DView.Unit, node "" 1L 19L True))

    [<Test>]
    let ``Func(a,b) -> c > a + b``() =
        check parseConstraint "constraint Func(a, b) -> c > a + b;"
        <| Some (Definite
                     (DView.Func { Name = "Func"
                                   Params = [ "a"; "b" ] },
                      node "" 1L 28L
                        <| Bop (Gt,
                                node "" 1L 26L (LV(LVIdent "c")),
                                node "" 1L 32L
                                <| Bop(Add,
                                       node "" 1L 30L (LV(LVIdent "a")),
                                       node "" 1L 34L (LV(LVIdent "b"))))))

    [<Test>]
    let ``Func(a,b) -> ?;``() =
        check parseConstraint "constraint Func(a, b) -> ?;"
        <| Some (Indefinite
                    (DView.Func {   Name = "Func"
                                    Params = [ "a"; "b" ] } )
                     : ViewDef<DView, Expression>)
