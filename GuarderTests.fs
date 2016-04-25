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
        [ TestCaseData(Multiset.empty : CView)
              .Returns(Multiset.empty : SMGView)
              .SetName("Convert the empty CView to the empty GView")

          TestCaseData(Multiset.ofFlatList
                           [ Func <| smvfunc "foo" [ Expr.Int (siUnmarked "bar") ]
                             Func <| smvfunc "bar" [ Expr.Int (siUnmarked "baz") ]] )
              .Returns(Multiset.ofFlatList
                           [ smgfunc BTrue "foo" [ Expr.Int (siUnmarked "bar") ]
                             smgfunc BTrue "bar" [ Expr.Int (siUnmarked "baz") ]] )
              .SetName("Convert a flat CondView-list to a GuarView-list with no guards")

          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE
                                 (sbUnmarked "s", 
                                  Multiset.ofFlatList
                                      [ Func <| smvfunc "foo" [ Expr.Int (siUnmarked "bar") ]], 
                                  Multiset.ofFlatList
                                      [ Func <| smvfunc "bar" [ Expr.Int (siUnmarked "baz") ]] ) ] )
              .Returns(Multiset.ofFlatList
                           [ smgfunc
                                (sbUnmarked "s")
                                "foo"
                                [ Expr.Int (siUnmarked "bar") ]
                             smgfunc
                                (BNot (sbUnmarked "s"))
                                "bar"
                                [ Expr.Int (siUnmarked "baz") ]] )
              .SetName("Convert a singly-nested CondView-list to a GuarView-list with unit guards")

          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE
                                 (sbUnmarked "s", 
                                  Multiset.ofFlatList
                                       [ CFunc.ITE
                                             (sbUnmarked "t", 
                                              Multiset.ofFlatList
                                                  [ Func <| smvfunc
                                                        "foo"
                                                        [ Expr.Int (siUnmarked "bar") ]
                                                    Func <| smvfunc
                                                        "bar"
                                                        [ Expr.Int (siUnmarked "baz") ]], 
                                              Multiset.ofFlatList
                                                  [ Func <| smvfunc
                                                        "fizz"
                                                        [ Expr.Int (siUnmarked "buzz") ]])
                                         Func <| smvfunc
                                             "in"
                                               [ Expr.Int (siUnmarked "out") ]], 
                                  Multiset.ofFlatList
                                      [ Func <| smvfunc
                                            "ding"
                                            [ Expr.Int (siUnmarked "dong") ]] ) ] )
              .Returns(Multiset.ofFlatList
                           [ smgfunc
                                 (BAnd [ sbUnmarked "s"; sbUnmarked "t" ] )
                                 "foo"
                                 [ Expr.Int (siUnmarked "bar") ]
                             smgfunc
                                 (BAnd [ sbUnmarked "s"; sbUnmarked "t" ] )
                                 "bar"
                                 [ Expr.Int (siUnmarked "baz") ]
                             smgfunc
                                 (BAnd [ sbUnmarked "s"; BNot (sbUnmarked "t") ] )
                                 "fizz"
                                 [ Expr.Int (siUnmarked "buzz") ]
                             smgfunc
                                 (sbUnmarked "s")
                                 "in"
                                 [ Expr.Int (siUnmarked "out") ]
                             smgfunc
                                 (BNot (sbUnmarked "s"))
                                 "ding"
                                 [ Expr.Int (siUnmarked "dong") ]] )
              .SetName("Convert a complex-nested CondView-list to a GuarView-list with complex guards") ]
    
    // Test conversion of CViews into GViews.
    [<TestCaseSource("CondViews")>]
    member x.``Test converting CViews into GViews`` cv = guardCView cv
