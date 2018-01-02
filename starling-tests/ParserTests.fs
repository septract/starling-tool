/// <summary>
///     Parser tests.
/// </summary>
module Starling.Tests.Lang.Parser

open NUnit.Framework

open Starling.Collections
open Starling.Tests.TestUtils
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Lang.AST
open Starling.Lang.Parser

open FParsec

let get =
    function
    | Success(r, _, _) -> Some r
    | Failure _ -> None

let check p str ast =
    let actual = run p str
    match (run p str) with
    | Success (r, _, _) -> assertEqual ast r
    | Failure (s, _, _) -> Assert.Fail(s)

let checkFail (p : Parser<'A, unit>) (str : string) : unit =
    let actual = run p str
    match (run p str) with
    | Success (r, _, _) -> Assert.Fail (r.ToString())
    | Failure (s, _, _) -> ()

// Perform the same trick matt uses in Main.fs to overwrite a right-associative
// operator with the correct behaviour
let ( ** ) = ( <| )


module SymbolicTests =
    [<Test>]
    let ``Test symbolic %{foo [|x|] bar} is parsed correctly`` () =
        check parseSymbolic "%{foo [|x|] bar}"
            [ SymString "foo "
              SymArg ( node "" 1L 9L (Identifier "x") )
              SymString " bar" ]

module ViewProtoTests =
    [<Test>]
    let ``Test single view prototype is parsed correctly`` () =
        check parseViewProtoSet "view foo(int a, int b);"
            [ NoIterator
                (Func =
                    func "foo"
                        [ { ParamType = TInt; ParamName = "a" }
                          { ParamType = TInt; ParamName = "b" } ],
                 IsAnonymous = false) ]

    [<Test>]
    let ``Test multiple view prototype is parsed correctly`` () =
        check parseViewProtoSet "view foo(int a, int b), bar(int c, bool d);"
            [ NoIterator
                (Func =
                    func "foo"
                        [ { ParamType = TInt; ParamName = "a" }
                          { ParamType = TInt; ParamName = "b" } ],
                 IsAnonymous = false)
              NoIterator
                (Func =
                    func "bar"
                        [ { ParamType = TInt; ParamName = "c" }
                          { ParamType = TBool; ParamName = "d" } ],
                 IsAnonymous = false) ]

    [<Test>]
    let ``Test nullary view prototype is not allowed`` () =
        checkFail parseViewProtoSet "view ;"


// Conversion of mattw's test cases into new system
module ExpressionTests =
    [<Test>]
    let ``Test modulo is parsed correctly`` () =
        check parseExpression "5 + 6 % 7"
            ** node "" 1L 3L
            ** BopExpr (Add,
                    node "" 1L 1L (Num 5L),
                    node "" 1L 7L
                        <| BopExpr (Mod,
                                node "" 1L 5L (Num 6L),
                                node "" 1L 9L (Num 7L)))

    [<Test>]
    let ``Test multiplicatives parse left to right`` () =
        check parseExpression "5 * 6 / 7 % 8"
            ** node "" 1L 11L
                 (BopExpr
                     (Mod,
                      node "" 1L 7L
                          (BopExpr
                              (Div,
                               node "" 1L 3L
                                   (BopExpr
                                        (Mul,
                                         node "" 1L 1L (Num 5L),
                                         node "" 1L 5L (Num 6L))),
                               node "" 1L 9L (Num 7L))),
                      node "" 1L 13L (Num 8L)))

    [<Test>]
    let ``Test order-of-operations on (1 + 2 * 3)``() =
        check parseExpression "1 + 2 * 3"
            ** node "" 1L 3L
            ** BopExpr (Add,
                    node "" 1L 1L (Num 1L),
                    node "" 1L 7L
                        <| BopExpr (Mul,
                                node "" 1L 5L (Num 2L),
                                node "" 1L 9L (Num 3L)))
    [<Test>]
    let ``Test bracketing on (1 + 2) * 3``() =
        check parseExpression "(1 + 2) * 3"
        ** node "" 1L 9L
            ** BopExpr (Mul,
                    node "" 1L 4L
                    <| BopExpr (Add,
                            node "" 1L 2L (Num 1L),
                            node "" 1L 6L (Num 2L)),
                    node "" 1L 11L (Num 3L))

    [<Test>]
    let ``Complex expression 1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8``() =
        check parseExpression "1 + 2 < 3 * 4 && true || 5 / 6 > 7 - 8"
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

    [<Test>]
    let ``Test negation / disjunction are parsed correctly`` () =
        check parseExpression "true || ! false"
             ** node "" 1L 6L
             ** BopExpr (Or,
                    node "" 1L 1L True,
                    node "" 1L 9L
                        <| UopExpr (Neg,
                                node "" 1L 11L False))



module AtomicActionTests =
    [<Test>]
    let ``error`` () =
        check parseAtomic "error;"
            (node "" 1L 1L AError)

    [<Test>]
    let ``assert(3 > 4)`` () =
        check parseAtomic "assert(3 > 4);"
            (node "" 1L 1L <| AAssert
                (* TODO(MattWindsor91): this is weird, and suggests we need to
                   rethink the AST encoding of BopExprs. *)
                (node "" 1L 10L <| BopExpr
                    (Gt,
                     node "" 1L 8L <| Num 3L,
                     node "" 1L 12L <| Num 4L)))

    [<Test>]
    let ``foo++``() =
        check parseAtomic "foo++;"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| Postfix
                    (node "" 1L 1L (Identifier "foo"),
                    Increment)))

    [<Test>]
    let ``foo--`` () =
        check parseAtomic "foo--;"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| Postfix
                    (node "" 1L 1L (Identifier "foo"),
                    Decrement)))

    [<Test>]
    let ``foo = bar`` () =
        check parseAtomic "foo = bar;"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| Fetch
                    (node "" 1L 1L (Identifier "foo"),
                    node "" 1L 7L (Identifier "bar"),
                    Direct)))

    [<Test>]
    let ``foo = bar++`` () =
        check parseAtomic "foo = bar++;"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| Fetch
                    (node "" 1L 1L (Identifier "foo"),
                    node "" 1L 7L (Identifier "bar"),
                    Increment)))

    [<Test>]
    let ``foo = bar--`` () =
        check parseAtomic "foo = bar--;"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| Fetch
                    (node "" 1L 1L (Identifier "foo"),
                    node "" 1L 7L (Identifier "bar"),
                    Decrement)))

    [<Test>]
    let ``Compare and swap`` () =
        check parseAtomic "CAS(foo, bar, 2);"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| CompareAndSwap
                    (node "" 1L 5L (Identifier "foo"),
                    node "" 1L 10L (Identifier "bar"),
                    node "" 1L 15L (Num 2L))))

    [<Test>]
    let ``parse havoc`` () =
        check parseAtomic "havoc y;"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| Havoc "y"))

    [<Test>]
    let ``parse symbolic atomic`` () =
        check parseAtomic "%{foo([|x|])};"
            (node "" 1L 1L <| APrim
                (node "" 1L 1L <| SymCommand
                [ SymString "foo("
                  SymArg ( node "" 1L 9L (Identifier "x") )
                  SymString ")" ] ))


module AtomicSetTests =
    [<Test>]
    let ``Single atomic block`` () =
        check parseAtomicSet "<| foo++; |>"
            [ node "" 1L 4L <| APrim
                (node "" 1L 4L <| Postfix
                    (node "" 1L 4L (Identifier "foo"),
                     Increment)) ]

    [<Test>]
    let ``Multiple in block valid`` () =
        check parseAtomicSet "<| foo++; bar--; |>"
            [ node "" 1L 4L <| APrim
                (node "" 1L 4L <| Postfix
                    (node "" 1L 4L (Identifier "foo"),
                     Increment))
              node "" 1L 11L <| APrim
                (node "" 1L 11L <| Postfix
                    (node "" 1L 11L (Identifier "bar"),
                     Decrement)) ]

module ConstraintTests =
    [<Test>]
    let ``emp -> true``() =
        check parseConstraint "constraint emp -> true;"
           (ViewSignature.Unit, Some <| node "" 1L 19L True)

    [<Test>]
    let ``Func(a,b) -> c > a + b``() =
        check parseConstraint "constraint Func(a, b) -> c > a + b;"
        <| (ViewSignature.Func (func "Func" [ "a"; "b" ] ),
                 Some
                   (node "" 1L 28L
                    <| BopExpr (Gt,
                                node "" 1L 26L (Identifier "c"),
                                node "" 1L 32L
                                <| BopExpr(Add,
                                       node "" 1L 30L (Identifier "a"),
                                       node "" 1L 34L (Identifier "b")))))

    [<Test>]
    let ``Func(a,b) -> ?;``() =
        check parseConstraint "constraint Func(a, b) -> ?;"
        <| (ViewSignature.Func (func "Func" [ "a"; "b" ] ),
                 (None : Expression option))
