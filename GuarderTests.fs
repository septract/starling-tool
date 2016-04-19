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
        let mseg : MGView = Multiset.empty
        [ TestCaseData(msec)
              .Returns(mseg)
              .SetName("Convert the empty CView to the empty GView")

          TestCaseData(Multiset.ofFlatList
                           [ Func <| mvfunc "foo" [ Expr.Int (iUnmarked "bar") ]
                             Func <| mvfunc "bar" [ Expr.Int (iUnmarked "baz") ]] )
              .Returns(Multiset.ofFlatList
                           [ mgfunc BTrue "foo" [ Expr.Int (iUnmarked "bar") ]
                             mgfunc BTrue "bar" [ Expr.Int (iUnmarked "baz") ]] )
              .SetName("Convert a flat CondView-list to a GuarView-list with no guards")

          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE
                                 (bUnmarked "s", 
                                  Multiset.ofFlatList
                                      [ Func <| mvfunc "foo" [ Expr.Int (iUnmarked "bar") ]], 
                                  Multiset.ofFlatList
                                      [ Func <| mvfunc "bar" [ Expr.Int (iUnmarked "baz") ]] ) ] )
              .Returns(Multiset.ofFlatList
                           [ mgfunc
                                (bUnmarked "s")
                                "foo"
                                [ Expr.Int (iUnmarked "bar") ]
                             mgfunc
                                (BNot (bUnmarked "s"))
                                "bar"
                                [ Expr.Int (iUnmarked "baz") ]] )
              .SetName("Convert a singly-nested CondView-list to a GuarView-list with unit guards")

          TestCaseData(Multiset.ofFlatList
                           [ CFunc.ITE
                                 (bUnmarked "s", 
                                  Multiset.ofFlatList
                                       [ CFunc.ITE
                                             (bUnmarked "t", 
                                              Multiset.ofFlatList
                                                  [ Func <| mvfunc
                                                        "foo"
                                                        [ Expr.Int (iUnmarked "bar") ]
                                                    Func <| mvfunc
                                                        "bar"
                                                        [ Expr.Int (iUnmarked "baz") ]], 
                                              Multiset.ofFlatList
                                                  [ Func <| mvfunc
                                                        "fizz"
                                                        [ Expr.Int (iUnmarked "buzz") ]])
                                         Func <| mvfunc
                                             "in"
                                               [ Expr.Int (iUnmarked "out") ]], 
                                  Multiset.ofFlatList
                                      [ Func <| mvfunc
                                            "ding"
                                            [ Expr.Int (iUnmarked "dong") ]] ) ] )
              .Returns(Multiset.ofFlatList
                           [ mgfunc
                                 (BAnd [ bUnmarked "s"; bUnmarked "t" ] )
                                 "foo"
                                 [ Expr.Int (iUnmarked "bar") ]
                             mgfunc
                                 (BAnd [ bUnmarked "s"; bUnmarked "t" ] )
                                 "bar"
                                 [ Expr.Int (iUnmarked "baz") ]
                             mgfunc
                                 (BAnd [ bUnmarked "s"; BNot (bUnmarked "t") ] )
                                 "fizz"
                                 [ Expr.Int (iUnmarked "buzz") ]
                             mgfunc
                                 (bUnmarked "s")
                                 "in"
                                 [ Expr.Int (iUnmarked "out") ]
                             mgfunc
                                 (BNot (bUnmarked "s"))
                                 "ding"
                                 [ Expr.Int (iUnmarked "dong") ]] )
              .SetName("Convert a complex-nested CondView-list to a GuarView-list with complex guards") ]
    
    // Test conversion of CViews into GViews.
    [<TestCaseSource("CondViews")>]
    member x.``Test converting CViews into GViews`` cv = guardCView cv
