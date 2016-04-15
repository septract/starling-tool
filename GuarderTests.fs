module Starling.Tests.Guarder

open NUnit.Framework
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Lang.Modeller
open Starling.Lang.Guarder


/// Tests for the view guarder.
type GuarderTests() = 
    
    /// Test cases for converting CondViews to GuarViews
    static member CondViews = 
        let msec : CView = Multiset.empty
        let mseg : GView = Multiset.empty
        [ TestCaseData(msec).Returns(mseg).SetName("Convert the empty CView to the empty GView")
          
          TestCaseData(Multiset.ofFlatList [ Func { Name = "foo"
                                                    Params = [ Expr.Int(AConst(Unmarked "bar")) ] }
                                             Func { Name = "bar"
                                                    Params = [ Expr.Int(AConst(Unmarked "baz")) ] } ])
              .Returns(Multiset.ofFlatList [ { Cond = BTrue
                                               Item = 
                                                   { Name = "foo"
                                                     Params = [ Expr.Int(AConst(Unmarked "bar")) ] } }
                                             { Cond = BTrue
                                               Item = 
                                                   { Name = "bar"
                                                     Params = [ Expr.Int(AConst(Unmarked "baz")) ] } } ])
              .SetName("Convert a flat CondView-list to a GuarView-list with no guards")
          
          TestCaseData(Multiset.ofFlatList [ CFunc.ITE((BConst(Unmarked "s")), 
                                                       Multiset.ofFlatList [ Func { Name = "foo"
                                                                                    Params = [ Expr.Int(AConst(Unmarked "bar")) ] } ], 
                                                       Multiset.ofFlatList [ Func { Name = "bar"
                                                                                    Params = [ Expr.Int(AConst(Unmarked "baz")) ] } ]) ])
              .Returns(Multiset.ofFlatList [ { Cond = BConst(Unmarked "s")
                                               Item = 
                                                   { Name = "foo"
                                                     Params = [ Expr.Int(AConst(Unmarked "bar")) ] } }
                                             { Cond = BNot(BConst(Unmarked "s"))
                                               Item = 
                                                   { Name = "bar"
                                                     Params = [ Expr.Int(AConst(Unmarked "baz")) ] } } ])
              .SetName("Convert a singly-nested CondView-list to a GuarView-list with unit guards")
          
          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE(BConst(Unmarked "s"), 
                                       Multiset.ofFlatList
                                           [ CFunc.ITE(BConst(Unmarked "t"), 
                                                       Multiset.ofFlatList [ Func { Name = "foo"
                                                                                    Params = [ Expr.Int(AConst(Unmarked "bar")) ] }
                                                                             Func { Name = "bar"
                                                                                    Params = [ Expr.Int(AConst(Unmarked "baz")) ] } ], 
                                                       Multiset.ofFlatList [ Func { Name = "fizz"
                                                                                    Params = [ Expr.Int(AConst(Unmarked "buzz")) ] } ])
                                             Func { Name = "in"
                                                    Params = [ Expr.Int(AConst(Unmarked "out")) ] } ], 
                                       Multiset.ofFlatList
                                           [ Func { Name = "ding"
                                                    Params = [ Expr.Int(AConst(Unmarked "dong")) ] } ]) ])
              .Returns(Multiset.ofFlatList [ { Cond = 
                                                   BAnd [ BConst(Unmarked "s")
                                                          BConst(Unmarked "t") ]
                                               Item = 
                                                   { Name = "foo"
                                                     Params = [ Expr.Int(AConst(Unmarked "bar")) ] } }
                                             { Cond = 
                                                   BAnd [ BConst(Unmarked "s")
                                                          BConst(Unmarked "t") ]
                                               Item = 
                                                   { Name = "bar"
                                                     Params = [ Expr.Int(AConst(Unmarked "baz")) ] } }
                                             { Cond = 
                                                   BAnd [ BConst(Unmarked "s")
                                                          BNot(BConst(Unmarked "t")) ]
                                               Item = 
                                                   { Name = "fizz"
                                                     Params = [ Expr.Int(AConst(Unmarked "buzz")) ] } }
                                             { Cond = BConst(Unmarked "s")
                                               Item = 
                                                   { Name = "in"
                                                     Params = [ Expr.Int(AConst(Unmarked "out")) ] } }
                                             { Cond = BNot(BConst(Unmarked "s"))
                                               Item = 
                                                   { Name = "ding"
                                                     Params = [ Expr.Int(AConst(Unmarked "dong")) ] } } ])
              .SetName("Convert a complex-nested CondView-list to a GuarView-list with complex guards") ]
    
    // Test conversion of CViews into GViews.
    [<TestCaseSource("CondViews")>]
    member x.``Test converting CViews into GViews`` cv = guardCView cv
