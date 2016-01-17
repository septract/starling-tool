module Starling.Tests.Expander

open NUnit.Framework
open Starling.Collections
open Starling.Expr
open Starling.Expander
open Starling.Model

/// Tests for the expander.
type ExpanderTests() = 
    
    /// Test cases for converting CondViews to GuarViews
    static member CondViews = 
        let msec : CView = Multiset.empty()
        let mseg : GView = Multiset.empty()
        [ TestCaseData(msec).Returns(mseg).SetName("Convert the empty CondView to the empty GuarView")
          
          TestCaseData(Multiset.ofList [ Func { Name = "foo"
                                                Params = [ AExpr(AConst(Unmarked "bar")) ] }
                                         Func { Name = "bar"
                                                Params = [ AExpr(AConst(Unmarked "baz")) ] } ])
              .Returns(Multiset.ofList [ { Cond = BTrue
                                           Item = 
                                               { Name = "foo"
                                                 Params = [ AExpr(AConst(Unmarked "bar")) ] } }
                                         { Cond = BTrue
                                           Item = 
                                               { Name = "bar"
                                                 Params = [ AExpr(AConst(Unmarked "baz")) ] } } ])
              .SetName("Convert a flat CondView-list to a GuarView-list with no guards")
          
          TestCaseData(Multiset.ofList [ ITE((BConst(Unmarked "s")), 
                                             Multiset.ofList [ Func { Name = "foo"
                                                                      Params = [ AExpr(AConst(Unmarked "bar")) ] } ], 
                                             Multiset.ofList [ Func { Name = "bar"
                                                                      Params = [ AExpr(AConst(Unmarked "baz")) ] } ]) ])
              .Returns(Multiset.ofList [ { Cond = BConst(Unmarked "s")
                                           Item = 
                                               { Name = "foo"
                                                 Params = [ AExpr(AConst(Unmarked "bar")) ] } }
                                         { Cond = BNot(BConst(Unmarked "s"))
                                           Item = 
                                               { Name = "bar"
                                                 Params = [ AExpr(AConst(Unmarked "baz")) ] } } ])
              .SetName("Convert a singly-nested CondView-list to a GuarView-list with unit guards")
          
          TestCaseData(Multiset.ofList [ ITE(BConst(Unmarked "s"), 
                                             Multiset.ofList [ ITE(BConst(Unmarked "t"), 
                                                                   Multiset.ofList [ Func { Name = "foo"
                                                                                            Params = [ AExpr(AConst(Unmarked "bar")) ] }
                                                                                     Func { Name = "bar"
                                                                                            Params = [ AExpr(AConst(Unmarked "baz")) ] } ], 
                                                                   Multiset.ofList [ Func { Name = "fizz"
                                                                                            Params = [ AExpr(AConst(Unmarked "buzz")) ] } ])
                                                               Func { Name = "in"
                                                                      Params = [ AExpr(AConst(Unmarked "out")) ] } ], 
                                             Multiset.ofList [ Func { Name = "ding"
                                                                      Params = [ AExpr(AConst(Unmarked "dong")) ] } ]) ])
              .Returns(Multiset.ofList [ { Cond = 
                                               BAnd [ BConst(Unmarked "s")
                                                      BConst(Unmarked "t") ]
                                           Item = 
                                               { Name = "foo"
                                                 Params = [ AExpr(AConst(Unmarked "bar")) ] } }
                                         { Cond = 
                                               BAnd [ BConst(Unmarked "s")
                                                      BConst(Unmarked "t") ]
                                           Item = 
                                               { Name = "bar"
                                                 Params = [ AExpr(AConst(Unmarked "baz")) ] } }
                                         { Cond = 
                                               BAnd [ BConst(Unmarked "s")
                                                      BNot(BConst(Unmarked "t")) ]
                                           Item = 
                                               { Name = "fizz"
                                                 Params = [ AExpr(AConst(Unmarked "buzz")) ] } }
                                         { Cond = BConst(Unmarked "s")
                                           Item = 
                                               { Name = "in"
                                                 Params = [ AExpr(AConst(Unmarked "out")) ] } }
                                         { Cond = BNot(BConst(Unmarked "s"))
                                           Item = 
                                               { Name = "ding"
                                                 Params = [ AExpr(AConst(Unmarked "dong")) ] } } ])
              .SetName("Convert a complex-nested CondView-list to a GuarView-list with complex guards") ]
    
    // Test conversion of CondViews into GuarViews.
    [<TestCaseSource("CondViews")>]
    member x.``Test converting CondViews into GuarViews`` cv = resolveCondViews cv
