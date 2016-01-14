module Starling.Tests.Semantics

open NUnit.Framework
open Starling
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Semantics
open Starling.Tests.Studies

/// Tests for the semantic transformer.
type SemanticsTests() = 
    
    // Test cases for the expression framer.
    static member FrameExprs = 
        [ TestCaseData(BTrue).Returns([ aEq (aAfter "serving") (aBefore "serving")
                                        aEq (aAfter "ticket") (aBefore "ticket")
                                        aEq (aAfter "s") (aBefore "s")
                                        aEq (aAfter "t") (aBefore "t") ])
              .SetName("Frame id using the ticketed lock model")
          
          TestCaseData(BAnd [ BGt(aAfter "ticket", aBefore "ticket")
                              BLe(aAfter "serving", aBefore "serving")
                              bUnmarked "frozzle"
                              aEq (aBefore "s") (aBefore "t") ]).Returns([ aEq (aAfter "s") (aBefore "s")
                                                                           aEq (aAfter "t") (aBefore "t") ])
              .SetName("Frame a simple command expression using the ticketed lock model") ]
    
    // Test framing of expressions.
    [<TestCaseSource("FrameExprs")>]
    member x.``Test framing of expressions using the ticketed lock model`` expr = frame ticketLockModel expr
    
    /// Test cases for full command semantic translation.
    static member Commands = 
        [ // Annoyingly, order of terms seems to matter here.
          // TODO(CaptainHayashi): weaken this test?
          TestCaseData(PrimAssume(aEq (aUnmarked "s") (aUnmarked "t")))
              .Returns(BAnd [ aEq (aAfter "serving") (aBefore "serving")
                              aEq (aAfter "ticket") (aBefore "ticket")
                              aEq (aAfter "s") (aBefore "s")
                              aEq (aAfter "t") (aBefore "t")
                              aEq (aBefore "s") (aBefore "t") ])
              .SetName("Semantically translate <assume(s == t)> using the ticketed lock model")
          
          TestCaseData(IntLoad(None, LVIdent "serving", Increment))
              .Returns(BAnd [ aEq (aAfter "ticket") (aBefore "ticket")
                              aEq (aAfter "s") (aBefore "s")
                              aEq (aAfter "t") (aBefore "t")
                              aEq (aAfter "serving") (AAdd [ aBefore "serving"
                                                             AInt 1L ]) ])
              .SetName("Semantically translate <serving++> using the ticketed lock model") ]
    
    // Test semantic reification of commands.
    [<TestCaseSource("Commands")>]
    member x.``Test semantic translation of commands using the ticketed lock model`` com = 
        semanticsOf ticketLockModel com
