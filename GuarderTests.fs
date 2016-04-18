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
                                                    Params = [ Expr.Int(AVar(Unmarked "bar")) ] }
                                             Func { Name = "bar"
                                                    Params = [ Expr.Int(AVar(Unmarked "baz")) ] } ])
              .Returns(Multiset.ofFlatList [ { Cond = BTrue
                                               Item = 
                                                   { Name = "foo"
                                                     Params = [ Expr.Int(AVar(Unmarked "bar")) ] } }
                                             { Cond = BTrue
                                               Item = 
                                                   { Name = "bar"
                                                     Params = [ Expr.Int(AVar(Unmarked "baz")) ] } } ])
              .SetName("Convert a flat CondView-list to a GuarView-list with no guards")
          
          TestCaseData(Multiset.ofFlatList [ CFunc.ITE((BVar(Unmarked "s")), 
                                                       Multiset.ofFlatList [ Func { Name = "foo"
                                                                                    Params = [ Expr.Int(AVar(Unmarked "bar")) ] } ], 
                                                       Multiset.ofFlatList [ Func { Name = "bar"
                                                                                    Params = [ Expr.Int(AVar(Unmarked "baz")) ] } ]) ])
              .Returns(Multiset.ofFlatList [ { Cond = BVar(Unmarked "s")
                                               Item = 
                                                   { Name = "foo"
                                                     Params = [ Expr.Int(AVar(Unmarked "bar")) ] } }
                                             { Cond = BNot(BVar(Unmarked "s"))
                                               Item = 
                                                   { Name = "bar"
                                                     Params = [ Expr.Int(AVar(Unmarked "baz")) ] } } ])
              .SetName("Convert a singly-nested CondView-list to a GuarView-list with unit guards")
          
          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE(BVar(Unmarked "s"), 
                                       Multiset.ofFlatList
                                           [ CFunc.ITE(BVar(Unmarked "t"), 
                                                       Multiset.ofFlatList [ Func { Name = "foo"
                                                                                    Params = [ Expr.Int(AVar(Unmarked "bar")) ] }
                                                                             Func { Name = "bar"
                                                                                    Params = [ Expr.Int(AVar(Unmarked "baz")) ] } ], 
                                                       Multiset.ofFlatList [ Func { Name = "fizz"
                                                                                    Params = [ Expr.Int(AVar(Unmarked "buzz")) ] } ])
                                             Func { Name = "in"
                                                    Params = [ Expr.Int(AVar(Unmarked "out")) ] } ], 
                                       Multiset.ofFlatList
                                           [ Func { Name = "ding"
                                                    Params = [ Expr.Int(AVar(Unmarked "dong")) ] } ]) ])
              .Returns(Multiset.ofFlatList [ { Cond = 
                                                   BAnd [ BVar(Unmarked "s")
                                                          BVar(Unmarked "t") ]
                                               Item = 
                                                   { Name = "foo"
                                                     Params = [ Expr.Int(AVar(Unmarked "bar")) ] } }
                                             { Cond = 
                                                   BAnd [ BVar(Unmarked "s")
                                                          BVar(Unmarked "t") ]
                                               Item = 
                                                   { Name = "bar"
                                                     Params = [ Expr.Int(AVar(Unmarked "baz")) ] } }
                                             { Cond = 
                                                   BAnd [ BVar(Unmarked "s")
                                                          BNot(BVar(Unmarked "t")) ]
                                               Item = 
                                                   { Name = "fizz"
                                                     Params = [ Expr.Int(AVar(Unmarked "buzz")) ] } }
                                             { Cond = BVar(Unmarked "s")
                                               Item = 
                                                   { Name = "in"
                                                     Params = [ Expr.Int(AVar(Unmarked "out")) ] } }
                                             { Cond = BNot(BVar(Unmarked "s"))
                                               Item = 
                                                   { Name = "ding"
                                                     Params = [ Expr.Int(AVar(Unmarked "dong")) ] } } ])
              .SetName("Convert a complex-nested CondView-list to a GuarView-list with complex guards") ]
    
    // Test conversion of CViews into GViews.
    [<TestCaseSource("CondViews")>]
    member x.``Test converting CViews into GViews`` cv = guardCView cv
