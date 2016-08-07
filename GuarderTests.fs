/// <summary>
///     Tests for the guarder.
/// </summary>
module Starling.Tests.Guarder

open NUnit.Framework
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Lang.Modeller
open Starling.Lang.Guarder


/// Tests for the view guarder.
type GuarderTests() = 
    
    /// Test cases for converting CondViews to GuarViews
    static member CondViews = 
        [ TestCaseData(Multiset.empty : CView)
              .Returns(Multiset.empty : GView<Sym<Var>>)
              .SetName("Convert the empty CView to the empty GView")

          TestCaseData(Multiset.ofFlatList
                           [ Func <| svfunc "foo" [ Expr.Int (siVar "bar") ]
                             Func <| svfunc "bar" [ Expr.Int (siVar "baz") ]] )
              .Returns(Multiset.ofFlatList
                           [ svgfunc BTrue "foo" [ Expr.Int (siVar "bar") ]
                             svgfunc BTrue "bar" [ Expr.Int (siVar "baz") ]] )
              .SetName("Convert a flat CondView-list to a GuarView-list with no guards")

          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE
                                 (sbVar "s", 
                                  Multiset.ofFlatList
                                      [ Func <| svfunc "foo" [ Expr.Int (siVar "bar") ]], 
                                  Multiset.ofFlatList
                                      [ Func <| svfunc "bar" [ Expr.Int (siVar "baz") ]] ) ] )
              .Returns(Multiset.ofFlatList
                           [ svgfunc
                                (sbVar "s")
                                "foo"
                                [ Expr.Int (siVar "bar") ]
                             svgfunc
                                (BNot (sbVar "s"))
                                "bar"
                                [ Expr.Int (siVar "baz") ]] )
              .SetName("Convert a singly-nested CondView-list to a GuarView-list with unit guards")

          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE
                                 (sbVar "s", 
                                  Multiset.ofFlatList
                                       [ CFunc.ITE
                                             (sbVar "t", 
                                              Multiset.ofFlatList
                                                  [ Func <| svfunc
                                                        "foo"
                                                        [ Expr.Int (siVar "bar") ]
                                                    Func <| svfunc
                                                        "bar"
                                                        [ Expr.Int (siVar "baz") ]], 
                                              Multiset.ofFlatList
                                                  [ Func <| svfunc
                                                        "fizz"
                                                        [ Expr.Int (siVar "buzz") ]])
                                         Func <| svfunc
                                             "in"
                                               [ Expr.Int (siVar "out") ]], 
                                  Multiset.ofFlatList
                                      [ Func <| svfunc
                                            "ding"
                                            [ Expr.Int (siVar "dong") ]] ) ] )
              .Returns(Multiset.ofFlatList
                           [ svgfunc
                                 (BAnd [ sbVar "s"; sbVar "t" ] )
                                 "foo"
                                 [ Expr.Int (siVar "bar") ]
                             svgfunc
                                 (BAnd [ sbVar "s"; sbVar "t" ] )
                                 "bar"
                                 [ Expr.Int (siVar "baz") ]
                             svgfunc
                                 (BAnd [ sbVar "s"; BNot (sbVar "t") ] )
                                 "fizz"
                                 [ Expr.Int (siVar "buzz") ]
                             svgfunc
                                 (sbVar "s")
                                 "in"
                                 [ Expr.Int (siVar "out") ]
                             svgfunc
                                 (BNot (sbVar "s"))
                                 "ding"
                                 [ Expr.Int (siVar "dong") ]] )
              .SetName("Convert a complex-nested CondView-list to a GuarView-list with complex guards") ]
    
    // Test conversion of CViews into GViews.
    [<TestCaseSource("CondViews")>]
    member x.``Test converting CViews into GViews`` cv = guardCView cv
