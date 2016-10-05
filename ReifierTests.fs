/// <summary>
///     Tests for <c>Starling.Reifier</c>.
/// </summary>
module Starling.Tests.Reifier

open NUnit.Framework
open Starling.Utils.Testing
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.TypeSystem
open Starling.Core.View
open Starling.Reifier

/// <summary>
///     Tests for parameter equality calculation.
/// </summary>
module ParamEqualities =
    [<Test>]
    let ``Parameter equalities on a single func are empty`` () =
        assertEqual
            []
            (paramEqualities
                [ iterated
                    (smvfunc "A" [ Int (siBefore "x1"); Int (siBefore "y1") ])
                    (AInt 1L) ] )

    [<Test>]
    let ``Parameter equalities on a set of nullary funcs are empty`` () =
        assertEqual
            []
            (paramEqualities
                [ iterated (smvfunc "A" []) (AInt 1L)
                  iterated (smvfunc "A" []) (AInt 1L) ] )

    [<Test>]
    let ``Parameter equalities on parameterised funcs are correct`` () =
        assertEqual
            [ iEq (siBefore "x1") (siBefore "x2")
              iEq (siAfter "y1") (siAfter "y2")
              bEq (sbBefore "z1") (sbBefore "z2")
              iEq (siBefore "x1") (siBefore "x3")
              iEq (siAfter "y1") (siAfter "y3")
              bEq (sbBefore "z1") (sbBefore "z3")
              iEq (siBefore "x1") (siBefore "x4")
              iEq (siAfter "y1") (siAfter "y4")
              bEq (sbBefore "z1") (sbBefore "z4")
              ]
            (paramEqualities
                [ iterated
                    (smvfunc "A"
                        [ Int (siBefore "x1")
                          Int (siAfter "y1")
                          Bool (sbBefore "z1") ])
                    (AInt 1L)
                  iterated
                    (smvfunc "A"
                        [ Int (siBefore "x2")
                          Int (siAfter "y2")
                          Bool (sbBefore "z2") ])
                    (AInt 10L)
                  iterated
                    (smvfunc "A"
                        [ Int (siBefore "x3")
                          Int (siAfter "y3")
                          Bool (sbBefore "z3") ])
                    (siBefore "i")
                  iterated
                    (smvfunc "A"
                        [ Int (siBefore "x4")
                          Int (siAfter "y4")
                          Bool (sbBefore "z4") ])
                    (AMul [ siAfter "j"; AInt 6L ]) ] )
