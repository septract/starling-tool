/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Graph
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Axiom
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.Modeller

/// The raw form of the ticketed lock.
let ticketLock = """
view holdTick(int t);
view holdLock();

constraint emp                         -> ticket >= serving;
constraint holdTick(t)                 -> ticket > t;
constraint holdLock()                  -> ticket > serving;
constraint holdLock()   * holdTick(t)  -> serving != t;
constraint holdTick(ta) * holdTick(tb) -> ta != tb;
constraint holdLock()   * holdLock()   -> false;

shared int ticket;
shared int serving;
thread int t;
thread int s;

method lock() {
  {| emp |}
    <t = ticket++>;
  {| holdTick(t) |}
    do {
      {| holdTick(t) |}
        <s = serving>;
      {| if s == t then holdLock() else holdTick(t) |}
    } while (s != t);
  {| holdLock() |}
}

method unlock() {
  {| holdLock() |}
    <serving++>;
  {| emp |}
}
"""

/// The correct parsing of the ticketed lock's lock method.
let ticketLockLockMethodAST = 
    { Signature = {Name = "lock"; Params = []}
      Body = 
          { Pre = Unit
            Contents = 
                [ { Command = Atomic(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment))
                    Post = View.Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]} }
                  { Command = 
                        DoWhile
                            ({ Pre = View.Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]}
                               Contents = 
                                   [ { Command = Atomic(Fetch(LVIdent "s", LV(LVIdent "serving"), Direct))
                                       Post = 
                                           View.If
                                               (Bop(Eq, LV(LVIdent "s"), LV(LVIdent "t")), View.Func {Name = "holdLock"; Params = []}, 
                                                View.Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]}) } ] }, 
                             Bop(Neq, LV(LVIdent "s"), LV(LVIdent "t")))
                    Post = View.Func { Name = "holdLock"; Params = []} } ] } }

/// The correct parsing of the ticketed lock's unlock method.
let ticketLockUnlockMethodAST = 
    { Signature = {Name = "unlock"; Params = []}
      Body = 
          { Pre = View.Func {Name = "holdLock"; Params = []}
            Contents = 
                [ { Command = Atomic(Postfix(LVIdent "serving", Increment))
                    Post = Unit } ] } }

/// The parsed form of the ticketed lock.
let ticketLockParsed = 
    [ ViewProto { Name = "holdTick"
                  Params = [ (Type.Int, "t") ] }
      ViewProto { Name = "holdLock"
                  Params = [] }
      Constraint { CView = ViewDef.Unit
                   CExpression = Some <| Bop(Ge, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
      Constraint { CView = ViewDef.Func {Name = "holdTick"; Params = [ "t" ]}
                   CExpression = Some <| Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")) }
      Constraint { CView = ViewDef.Func {Name = "holdLock"; Params = []}
                   CExpression = Some <| Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func {Name = "holdTick"; Params = [ "t" ]})
                   CExpression = Some <| Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func {Name = "holdTick"; Params = [ "ta" ]}, ViewDef.Func { Name = "holdTick"; Params = [ "tb" ]})
                   CExpression = Some <| Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func { Name = "holdLock"; Params = []})
                   CExpression = Some <| False }
      Global(Type.Int, "ticket")
      Global(Type.Int, "serving")
      Local(Type.Int, "t")
      Local(Type.Int, "s")
      Method ticketLockLockMethodAST
      Method ticketLockUnlockMethodAST ]

/// The collated form of the ticketed lock.
let ticketLockCollated = 
    { CollatedScript.Globals = 
          [ (Type.Int, "ticket")
            (Type.Int, "serving") ]
      Locals = 
          [ (Type.Int, "t")
            (Type.Int, "s") ]
      Search = None
      VProtos = 
          [ { Name = "holdTick"
              Params = [ (Type.Int, "t") ] }
            { Name = "holdLock"
              Params = [] } ]
      Constraints = 
          [ { // constraint emp => ticket >= serving;
              CView = ViewDef.Unit
              CExpression = Some <| Bop(Ge, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
            { // constraint holdTick(t) => ticket > t;
              CView = ViewDef.Func {Name = "holdTick"; Params = [ "t" ]}
              CExpression = Some <| Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")) }
            { // constraint holdLock() => ticket > serving;
              CView = ViewDef.Func {Name = "holdLock"; Params = []}
              CExpression = Some <| Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
            { // constraint holdLock() * holdTick(t) => serving != t;
              CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func {Name = "holdTick"; Params = [ "t" ]})
              CExpression = Some <| Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")) }
            { // constraint holdLock() * holdLock() => false;
              CView = ViewDef.Join(ViewDef.Func {Name = "holdTick"; Params = [ "ta" ]}, ViewDef.Func {Name = "holdTick"; Params = [ "tb" ]})
              CExpression = Some <| Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")) }
            { CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func {Name = "holdLock"; Params = []})
              CExpression = Some <| False } ]
      Methods = [ ticketLockLockMethodAST; ticketLockUnlockMethodAST ] }

/// Shorthand for Multiset.singleton.
let sing = Multiset.singleton

/// The conditional holdLock view.
let holdLock =
    func "holdLock" [] |> Func

/// The conditional holdTick view.
let holdTick =
    func "holdTick" [AExpr (aUnmarked "t")] |> Func

/// The guarded holdLock view.
let gHoldLock cnd = gfunc cnd "holdLock" []

/// The guarded holdTick view.
let gHoldTick cnd = gfunc cnd "holdTick" [AExpr (aUnmarked "t")]

/// Produces the expression 's == t'.
let sIsT = aEq (aUnmarked "s") (aUnmarked "t")

/// The ticketed lock's lock method.
let ticketLockLock =
    { Signature = func "lock" []
      Body =
          { Pre = Multiset.empty()
            Contents =
                [ { Command =
                        func "!ILoad++"
                             [ AExpr (aBefore "t"); AExpr (aAfter "t")
                               AExpr (aBefore "ticket"); AExpr (aAfter "ticket") ]
                        |> Prim
                    Post = sing holdTick }
                  { Command =
                        While (isDo = true,
                               expr = BNot sIsT,
                               inner =
                                   { Pre = sing holdTick
                                     Contents =
                                         [ { Command =
                                                 func "!ILoad"
                                                      [ AExpr (aBefore "s"); AExpr (aAfter "s")
                                                        AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                                                 |> Prim
                                             Post =
                                                 (sIsT,
                                                  sing holdLock,
                                                  sing holdTick)
                                                 |> CFunc.ITE
                                                 |> Multiset.singleton } ] } )
                    Post = sing holdLock } ] } }

/// The ticket lock's unlock method.
let ticketLockUnlock =
    { Signature = func "unlock" []
      Body =
          { Pre = sing holdLock
            Contents =
                [ { Command =
                        func "!I++" [ AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                        |> Prim
                    Post = Multiset.empty() }]}}

/// The methods of the ticketed lock.
let ticketLockMethods =
    [ ("lock", ticketLockLock)
      ("unlock", ticketLockUnlock) ] |> Map.ofList


/// The ticketed lock's lock method, in guarded form.
let ticketLockGuardedLock =
    { Signature = func "lock" []
      Body =
          { Pre = Multiset.empty()
            Contents =
                [ { Command =
                        func "!ILoad++"
                             [ AExpr (aBefore "t"); AExpr (aAfter "t")
                               AExpr (aBefore "ticket"); AExpr (aAfter "ticket") ]
                        |> Prim
                    Post = sing (gHoldTick BTrue) }
                  { Command =
                        While (isDo = true,
                               expr = BNot sIsT,
                               inner =
                                   { Pre = sing (gHoldTick BTrue)
                                     Contents =
                                         [ { Command =
                                                 func "!ILoad"
                                                      [ AExpr (aBefore "s"); AExpr (aAfter "s")
                                                        AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                                                 |> Prim
                                             Post =
                                                 Multiset.ofList
                                                     [ gHoldLock sIsT
                                                       gHoldTick (BNot sIsT) ] } ] } )
                    Post = sing (gHoldLock BTrue) } ] } }

/// The ticket lock's unlock method, in guarded form.
let ticketLockGuardedUnlock : Method<GView, PartCmd<GView>> =
    { Signature = func "unlock" []
      Body =
          { Pre = sing (gHoldLock BTrue)
            Contents =
                [ { Command =
                        func "!I++" [ AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                        |> Prim
                    Post = Multiset.empty() } ] } }

/// The view definitions of the ticketed lock model.
let ticketLockViewDefs =
    [ { View = Multiset.empty()
        Def = Some <| BGe(aUnmarked "ticket", aUnmarked "serving") }
      { View = 
            Multiset.ofList [ { Name = "holdTick"
                                Params = [ (Type.Int, "t") ] } ]
        Def = Some <| BGt(aUnmarked "ticket", aUnmarked "t") }
      { View = 
            Multiset.ofList [ { Name = "holdLock"
                                Params = [] } ]
        Def = Some <| BGt(aUnmarked "ticket", aUnmarked "serving") }
      { View = 
            Multiset.ofList [ { Name = "holdLock"
                                Params = [] }
                              { Name = "holdTick"
                                Params = [ (Type.Int, "t") ] } ]
        Def = Some <| BNot(aEq (aUnmarked "serving") (aUnmarked "t")) }
      { View = 
            Multiset.ofList [ { Name = "holdTick"
                                Params = [ (Type.Int, "ta") ] }
                              { Name = "holdTick"
                                Params = [ (Type.Int, "tb") ] } ]
        Def = Some <| BNot(aEq (aUnmarked "ta") (aUnmarked "tb")) }
      { View = 
            Multiset.ofList [ { Name = "holdLock"
                                Params = [] }
                              { Name = "holdLock"
                                Params = [] } ]
        Def = Some <| BFalse } ]

/// The model of a ticketed lock method.
let ticketLockModel : Model<Method<CView, PartCmd<CView>>, DView> = 
    { Globals = 
          Map.ofList [ ("serving", Type.Int)
                       ("ticket", Type.Int) ]
      Locals = 
          Map.ofList [ ("s", Type.Int)
                       ("t", Type.Int) ]
      Axioms = ticketLockMethods
      ViewDefs = ticketLockViewDefs
      Semantics = Starling.Lang.Modeller.coreSemantics }

/// The CFG for the ticketed lock lock method.
let ticketLockLockSubgraph : Subgraph =
    { Nodes =
          Map.ofList
              [ ("lock_V0",
                     Multiset.empty ())
                ("lock_V1",
                     Multiset.singleton
                         (gfunc BTrue "holdTick" [ AExpr (aUnmarked "t") ] ))
                ("lock_V2",
                     Multiset.singleton (gfunc BTrue "holdLock" [] ))
                ("lock_V3",
                     Multiset.singleton
                         (gfunc BTrue "holdTick" [ AExpr (aUnmarked "t") ] ))
                ("lock_V4",
                     Multiset.ofList
                         [ gfunc (aEq (aUnmarked "s") (aUnmarked "t"))
                                 "holdLock"
                                 []
                           gfunc (BNot (aEq (aUnmarked "s") (aUnmarked "t")))
                                 "holdTick"
                                 [ AExpr (aUnmarked "t") ]] ) ]
      Edges =
          Map.ofList
              [ ("lock_C0",
                     edge "lock_V0"
                          (func "!ILoad++"
                                [ AExpr (aBefore "t")
                                  AExpr (aAfter "t")
                                  AExpr (aBefore "ticket")
                                  AExpr (aAfter "ticket") ] )
                          "lock_V1")
                ("lock_C1",
                     edge "lock_V3"
                          (func "!ILoad"
                                [ AExpr (aBefore "s")
                                  AExpr (aAfter "s")
                                  AExpr (aBefore "serving")
                                  AExpr (aAfter "serving") ] )
                          "lock_V4")
                ("lock_C2",
                     edge "lock_V4"
                          (func "Assume"
                                [ BExpr (BNot (aEq (aBefore "s")
                                                   (aBefore "t"))) ] )
                          "lock_V3")
                ("lock_C3",
                     edge "lock_V4"
                          (func "Assume"
                                [ BExpr (aEq (aBefore "s") (aBefore "t")) ] )
                          "lock_V2")
                ("lock_C4",
                     edge "lock_V1"
                          (func "Id" [])
                          "lock_V3") ] }

/// The CFG for the ticketed lock unlock method.
let ticketLockUnlockSubgraph : Subgraph =
    { Nodes =
          Map.ofList
              [ ("unlock_V0",
                     Multiset.singleton
                         (gfunc BTrue "holdLock" [] ))
                ("unlock_V1", Multiset.empty () ) ]
      Edges =
           Map.ofList
              [ ("unlock_C0",
                     edge "unlock_V0"
                          (func "!I++"
                                [ AExpr (aBefore "serving")
                                  AExpr (aAfter "serving") ] )
                          "unlock_V1" ) ] }
