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

    // Test cases for the expression framer.
    static member FrameExprs = 
        [ TestCaseData(BTrue).Returns([ aEq (aAfter "serving") (aBefore "serving")
                                        aEq (aAfter "ticket") (aBefore "ticket")
                                        aEq (aAfter "s") (aBefore "s")
                                        aEq (aAfter "t") (aBefore "t") ])
              .SetName("Frame id using the ticket lock model")
          
          TestCaseData(BAnd [ BGt(aAfter "ticket", aBefore "ticket")
                              BLe(aAfter "serving", aBefore "serving")
                              bUnmarked "frozzle"
                              aEq (aBefore "s") (aBefore "t") ]).Returns([ aEq (aAfter "s") (aBefore "s")
                                                                           aEq (aAfter "t") (aBefore "t") ])
              .SetName("Frame a simple command expression using the ticket lock model") ]
    
    // Test framing of expressions.
    [<TestCaseSource("FrameExprs")>]
    member x.``Test framing of expressions using the ticket lock model`` expr = frame ticketLockModel expr
    
    /// Test cases for full command semantic translation.
    static member Commands =
        [ TestCaseData([ func "Assume" [ aEq (aBefore "s") (aBefore "t")
                                         |> Expr.Bool ]] )
              .Returns(Some <| Set.ofList [ aEq (aAfter "serving") (aBefore "serving")
                                            aEq (aAfter "ticket") (aBefore "ticket")
                                            aEq (aAfter "s") (aBefore "s")
                                            aEq (aAfter "t") (aBefore "t")
                                            aEq (aBefore "s") (aBefore "t") ])
              .SetName("Semantically translate <assume(s == t)> using the ticket lock model")
          TestCaseData([ func "!I++" [ "serving" |> aBefore |> Expr.Int
                                       "serving" |> aAfter |> Expr.Int ]] )
              .Returns(Some <| Set.ofList[ aEq (aAfter "ticket") (aBefore "ticket")
                                           aEq (aAfter "s") (aBefore "s")
                                           aEq (aAfter "t") (aBefore "t")
                                           aEq (aAfter "serving") (AAdd [ aBefore "serving"
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
