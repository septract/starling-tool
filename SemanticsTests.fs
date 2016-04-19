module Starling.Tests.Semantics

open NUnit.Framework
open Starling
open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Semantics
open Starling.Tests.Studies

/// Tests for the semantic transformer.
type SemanticsTests() = 
    /// Test cases for composition.
    static member Compositions =
        [ TestCaseData((bEq (bAfter "foo") (bBefore "bar"),
                        bEq (bAfter "baz") (bBefore "foo")))
            .Returns(BAnd [ bEq (bInter 0I "foo") (bBefore "bar")
                            bEq (bAfter "baz") (bInter 0I "foo") ] )
            .SetName("Compose two basic assignments")
          TestCaseData((BAnd [ bEq (bInter 0I "foo") (bBefore "bar")
                               bEq (bAfter "baz") (bInter 0I "foo") ],
                        BAnd [ bEq (bInter 0I "flop") (bBefore "baz")
                               bEq (bAfter "froz") (bInter 0I "flop") ] ))
            // TODO(CaptainHayashi): make this not order-dependent... somehow
            .Returns(BAnd [ bEq (bInter 1I "baz") (bInter 0I "foo")
                            bEq (bInter 0I "foo") (bBefore "bar")
                            bEq (bAfter "froz") (bInter 2I "flop")
                            bEq (bInter 2I "flop") (bInter 1I "baz") ] )
            .SetName("Compose two compositions") ]

    /// Tests whether composition behaves itself.
    [<TestCaseSource("Compositions")>]
    member x.``Boolean composition should work correctly`` xy =
        xy ||> composeBools

    /// <summary>
    ///     Test cases for the variable framer.
    /// </summary>
    static member FrameVars =
        [ TestCaseData(CTyped.Int "foo")
              .Returns(iEq (iAfter "foo") (iBefore "foo"))
              .SetName("Frame an integer variable")
          TestCaseData(CTyped.Bool "bar")
              .Returns(bEq (bAfter "bar") (bBefore "bar"))
              .SetName("Frame an integer variable") ]

    /// <summary>
    ///     Tests <c>frameVar</c>.
    /// </summary>
    [<TestCaseSource("FrameVars")>]
    member x.``Test framing of individual variables`` var =
        frameVar var

    // Test cases for the expression framer.
    static member FrameExprs = 
        [ TestCaseData(BTrue : MBoolExpr)
              .Returns([ iEq (iAfter "serving") (iBefore "serving")
                         iEq (iAfter "ticket") (iBefore "ticket")
                         iEq (iAfter "s") (iBefore "s")
                         iEq (iAfter "t") (iBefore "t") ])
              .SetName("Frame id using the ticket lock model")
          
          TestCaseData(BAnd [ BGt(iAfter "ticket", iBefore "ticket")
                              BLe(iAfter "serving", iBefore "serving")
                              bUnmarked "frozzle"
                              iEq (iBefore "s") (iBefore "t") ]).Returns([ iEq (iAfter "s") (iBefore "s")
                                                                           iEq (iAfter "t") (iBefore "t") ])
              .SetName("Frame a simple command expression using the ticket lock model") ]
    
    // Test framing of expressions.
    [<TestCaseSource("FrameExprs")>]
    member x.``Test framing of expressions using the ticket lock model`` expr = frame ticketLockModel expr
    
    /// Test cases for full command semantic translation.
    static member Commands =
        [ TestCaseData([ func "Assume" [ iEq (iBefore "s") (iBefore "t")
                                         |> Expr.Bool ]] )
              .Returns(Some <| Set.ofList [ iEq (iAfter "serving") (iBefore "serving")
                                            iEq (iAfter "ticket") (iBefore "ticket")
                                            iEq (iAfter "s") (iBefore "s")
                                            iEq (iAfter "t") (iBefore "t")
                                            iEq (iBefore "s") (iBefore "t") ])
              .SetName("Semantically translate <assume(s == t)> using the ticket lock model")
          TestCaseData([ func "!I++" [ "serving" |> iBefore |> Expr.Int
                                       "serving" |> iAfter |> Expr.Int ]] )
              .Returns(Some <| Set.ofList[ iEq (iAfter "ticket") (iBefore "ticket")
                                           iEq (iAfter "s") (iBefore "s")
                                           iEq (iAfter "t") (iBefore "t")
                                           iEq (iAfter "serving") (AAdd [ iBefore "serving"
                                                                          AInt 1L ]) ])
              .SetName("Semantically translate <serving++> using the ticket lock model") ]
    
    // Test semantic reification of commands.
    [<TestCaseSource("Commands")>]
    member x.``Test semantic translation of commands using the ticket lock model`` com = 
        com
        |> semanticsOfCommand ticketLockModel
        |> okOption
        |> Option.bind (function
                        | BAnd xs -> xs |> Set.ofList |> Some
                        | _ -> None) 
