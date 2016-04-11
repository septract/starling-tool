/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Graph
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Axiom
open Starling.Core.GuardedView
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.Modeller

/// The raw form of the ticket lock.
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

/// The correct parsing of the ticket lock's lock method.
let ticketLockLockMethodAST =
    { Signature = {Name = "lock"; Params = []}
      Body =
          { Pre = Unmarked Unit
            Contents =
                [ { Command =
                        Command.Prim
                            { PreAssigns = []
                              Atomics = [ Fetch(LVIdent "t",
                                                LV(LVIdent "ticket"),
                                                Increment) ]
                              PostAssigns = [] }
                    Post = Unmarked <|
                           View.Func {Name = "holdTick"
                                      Params = [ LV(LVIdent "t") ]} }
                  { Command =
                        DoWhile
                            ({ Pre = Unmarked <|
                                     View.Func {Name = "holdTick"
                                                Params = [ LV(LVIdent "t") ]}
                               Contents =
                                   [ { Command =
                                           Command.Prim
                                               { PreAssigns = []
                                                 Atomics = [ Fetch(LVIdent "s",
                                                                   LV(LVIdent "serving"),
                                                                   Direct) ]
                                                 PostAssigns = [] }
                                       Post =
                                           Unmarked <|
                                           View.If
                                               (Bop(Eq, LV(LVIdent "s"), LV(LVIdent "t")), View.Func {Name = "holdLock"; Params = []},
                                                View.Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]}) } ] },
                             Bop(Neq, LV(LVIdent "s"), LV(LVIdent "t")))
                    Post = Unmarked <|
                           View.Func { Name = "holdLock"; Params = [] } } ] } }

/// The correct parsing of the ticket lock's unlock method.
let ticketLockUnlockMethodAST =
    { Signature = {Name = "unlock"; Params = []}
      Body =
          { Pre = Unmarked <| View.Func {Name = "holdLock"; Params = []}
            Contents =
                [ { Command =
                        Command.Prim
                            { PreAssigns = []
                              Atomics = [ Postfix(LVIdent "serving",
                                                  Increment) ]
                              PostAssigns = [] }
                    Post = Unmarked Unit } ] } }

/// The parsed form of the ticket lock.
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

/// The collated form of the ticket lock.
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
let gHoldLock cnd : GFunc = gfunc cnd "holdLock" []

/// The guarded holdTick view.
let gHoldTick cnd : GFunc = gfunc cnd "holdTick" [AExpr (aUnmarked "t")]

/// Produces the expression 's == t'.
let sIsT = aEq (aUnmarked "s") (aUnmarked "t")

/// The ticket lock's lock method.
let ticketLockLock =
    { Signature = func "lock" []
      Body =
          { Pre = Mandatory <| Multiset.empty
            Contents =
                [ { Command =
                        func "!ILoad++"
                             [ AExpr (aBefore "t"); AExpr (aAfter "t")
                               AExpr (aBefore "ticket"); AExpr (aAfter "ticket") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| sing holdTick }
                  { Command =
                        While (isDo = true,
                               expr = BNot sIsT,
                               inner =
                                   { Pre = Mandatory <| sing holdTick
                                     Contents =
                                         [ { Command =
                                                 func "!ILoad"
                                                      [ AExpr (aBefore "s"); AExpr (aAfter "s")
                                                        AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                                                 |> List.singleton |> Prim
                                             Post =
                                                 (sIsT,
                                                  sing holdLock,
                                                  sing holdTick)
                                                 |> CFunc.ITE
                                                 |> Multiset.singleton
                                                 |> Mandatory } ] } )
                    Post = Mandatory <| sing holdLock } ] } }

/// The ticket lock's unlock method.
let ticketLockUnlock =
    { Signature = func "unlock" []
      Body =
          { Pre = Mandatory <| sing holdLock
            Contents =
                [ { Command =
                        func "!I++" [ AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| Multiset.empty }]}}

/// The methods of the ticket lock.
let ticketLockMethods =
    [ ("lock", ticketLockLock)
      ("unlock", ticketLockUnlock) ] |> Map.ofList


/// The ticket lock's lock method, in guarded form.
let ticketLockGuardedLock =
    { Signature = func "lock" []
      Body =
          { Pre = Mandatory <| Multiset.empty
            Contents =
                [ { Command =
                        func "!ILoad++"
                             [ AExpr (aBefore "t"); AExpr (aAfter "t")
                               AExpr (aBefore "ticket"); AExpr (aAfter "ticket") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| sing (gHoldTick BTrue) }
                  { Command =
                        While (isDo = true,
                               expr = BNot sIsT,
                               inner =
                                   { Pre = Mandatory <| sing (gHoldTick BTrue)
                                     Contents =
                                         [ { Command =
                                                 func "!ILoad"
                                                      [ AExpr (aBefore "s"); AExpr (aAfter "s")
                                                        AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                                                 |> List.singleton |> Prim
                                             Post =
                                                 Mandatory <|
                                                 Multiset.ofFlatList
                                                     [ gHoldLock sIsT
                                                       gHoldTick (BNot sIsT) ] } ] } )
                    Post = Mandatory <| sing (gHoldLock BTrue) } ] } }

/// The ticket lock's unlock method, in guarded form.
let ticketLockGuardedUnlock : PMethod<ViewExpr<GView>> =
    { Signature = func "unlock" []
      Body =
          { Pre = Mandatory <| sing (gHoldLock BTrue)
            Contents =
                [ { Command =
                        func "!I++" [ AExpr (aBefore "serving"); AExpr (aAfter "serving") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| Multiset.empty } ] } }

/// The view definitions of the ticket lock model.
let ticketLockViewDefs =
    [ { View = Multiset.empty
        Def = Some <| BGe(aUnmarked "ticket", aUnmarked "serving") }
      { View =
            Multiset.ofFlatList
                [ { Name = "holdTick"
                    Params = [ (Type.Int, "t") ] } ]
        Def = Some <| BGt(aUnmarked "ticket", aUnmarked "t") }
      { View =
            Multiset.ofFlatList
                [ { Name = "holdLock"
                    Params = [] } ]
        Def = Some <| BGt(aUnmarked "ticket", aUnmarked "serving") }
      { View =
            Multiset.ofFlatList
                [ { Name = "holdLock"
                    Params = [] }
                  { Name = "holdTick"
                    Params = [ (Type.Int, "t") ] } ]
        Def = Some <| BNot(aEq (aUnmarked "serving") (aUnmarked "t")) }
      { View =
            Multiset.ofFlatList
                [ { Name = "holdTick"
                    Params = [ (Type.Int, "ta") ] }
                  { Name = "holdTick"
                    Params = [ (Type.Int, "tb") ] } ]
        Def = Some <| BNot(aEq (aUnmarked "ta") (aUnmarked "tb")) }
      { View =
            Multiset.ofFlatList
                [ { Name = "holdLock"
                    Params = [] }
                  { Name = "holdLock"
                    Params = [] } ]
        Def = Some <| BFalse } ]

/// The model of the ticket lock.
let ticketLockModel : Model<PMethod<ViewExpr<CView>>, DView> =
    { Globals =
          Map.ofList [ ("serving", Type.Int)
                       ("ticket", Type.Int) ]
      Locals =
          Map.ofList [ ("s", Type.Int)
                       ("t", Type.Int) ]
      Axioms = ticketLockMethods
      ViewDefs = ticketLockViewDefs
      Semantics = Starling.Lang.Modeller.coreSemantics }

/// The partial CFG for the ticket lock lock method.
let ticketLockLockSubgraph : Subgraph =
    { Nodes =
          Map.ofList
              [ ("lock_V0",
                     (Mandatory <| Multiset.empty, Entry))
                ("lock_V1", (Mandatory <| sing (gHoldTick BTrue), Normal))
                ("lock_V2", (Mandatory <| sing (gHoldLock BTrue), Exit))
                ("lock_V3", (Mandatory <| sing (gHoldTick BTrue), Normal))
                ("lock_V4",
                     (Mandatory <|
                      Multiset.ofFlatList
                         [ gHoldLock sIsT
                           gHoldTick (BNot sIsT) ], Normal)) ]
      Edges =
          Map.ofList
              [ ("lock_C0",
                     edge "lock_V0"
                          [ func "!ILoad++"
                                 [ AExpr (aBefore "t")
                                   AExpr (aAfter "t")
                                   AExpr (aBefore "ticket")
                                   AExpr (aAfter "ticket") ]]
                          "lock_V1")
                ("lock_C1",
                     edge "lock_V3"
                          [ func "!ILoad"
                                 [ AExpr (aBefore "s")
                                   AExpr (aAfter "s")
                                   AExpr (aBefore "serving")
                                   AExpr (aAfter "serving") ]]
                          "lock_V4")
                ("lock_C2",
                     edge "lock_V4"
                          [ func "Assume"
                                 [ BExpr (BNot (aEq (aBefore "s")
                                                    (aBefore "t"))) ]]
                          "lock_V3")
                ("lock_C3",
                     edge "lock_V4"
                          [ func "Assume"
                                 [ BExpr (aEq (aBefore "s")
                                              (aBefore "t")) ]]
                          "lock_V2")
                ("lock_C4",
                     edge "lock_V1"
                          []
                          "lock_V3") ] }

/// The partial CFG for the ticket lock unlock method.
let ticketLockUnlockSubgraph : Subgraph =
    { Nodes =
          Map.ofList
              [ ("unlock_V0",
                     (Mandatory <|
                      Multiset.singleton
                         (gfunc BTrue "holdLock" [] ), Entry))
                ("unlock_V1", (Mandatory <| Multiset.empty, Exit)) ]
      Edges =
           Map.ofList
              [ ("unlock_C0",
                     edge "unlock_V0"
                          [ func "!I++"
                                 [ AExpr (aBefore "serving")
                                   AExpr (aAfter "serving") ]]
                          "unlock_V1" ) ] }

let ticketLockLockGraph : Graph =
    { Name = "lock"
      Contents =
          Map.ofList
              [ ("lock_V0",
                 ((Mandatory <| Multiset.empty,
                   Set.singleton
                      { OutEdge.Name = "lock_C0"
                        OutEdge.Dest = "lock_V1"
                        OutEdge.Command =
                            [ func "!ILoad++"
                                   [ AExpr (aBefore "t")
                                     AExpr (aAfter "t")
                                     AExpr (aBefore "ticket")
                                     AExpr (aAfter "ticket") ]] },
                   Set.empty, 
                   Entry)))
                ("lock_V1",
                 (Mandatory <| sing (gHoldTick BTrue),
                  Set.singleton
                      { Name = "lock_C4"
                        Dest = "lock_V3"
                        Command = [] },
                  Set.singleton
                      { Name = "lock_C0"
                        Src = "lock_V0"
                        Command =
                            [ func "!ILoad++"
                                   [ AExpr (aBefore "t")
                                     AExpr (aAfter "t")
                                     AExpr (aBefore "ticket")
                                     AExpr (aAfter "ticket") ]] },
                  Normal ))
                ("lock_V2",
                 (Mandatory <| sing (gHoldLock BTrue),
                  Set.empty,
                  Set.singleton
                      { Name = "lock_C3"
                        Src = "lock_V4"
                        Command =
                            [ func "Assume"
                                   [ BExpr (aEq (aBefore "s")
                                                (aBefore "t")) ]] }, 
                   Exit))
                ("lock_V3",
                 (Mandatory <| sing (gHoldTick BTrue),
                  Set.singleton
                      { Name = "lock_C1"
                        Dest = "lock_V4"
                        Command =
                            [ func "!ILoad"
                                   [ AExpr (aBefore "s")
                                     AExpr (aAfter "s")
                                     AExpr (aBefore "serving")
                                     AExpr (aAfter "serving") ]] },
                  Set.ofList
                      [ { Name = "lock_C2"
                          Src = "lock_V4"
                          Command =
                              [ func "Assume"
                                     [ BExpr (BNot (aEq (aBefore "s")
                                                        (aBefore "t"))) ]] }
                        { Name = "lock_C4"
                          Src = "lock_V1"
                          Command = [] } ],
                   Normal))
                ("lock_V4",
                 (Mandatory <|
                  Multiset.ofFlatList
                      [ gHoldLock sIsT
                        gHoldTick (BNot sIsT) ],
                  Set.ofList
                      [ { Name = "lock_C2"
                          Dest = "lock_V3"
                          Command =
                              [ func "Assume"
                                     [ BExpr (BNot (aEq (aBefore "s")
                                                        (aBefore "t"))) ]] }
                        { Name = "lock_C3"
                          Dest = "lock_V2"
                          Command =
                              [ func "Assume"
                                     [ BExpr (aEq (aBefore "s")
                                                  (aBefore "t")) ]] } ],
                  Set.singleton
                      { Name = "lock_C1"
                        Src = "lock_V3"
                        Command =
                            [ func "!ILoad"
                                   [ AExpr (aBefore "s")
                                     AExpr (aAfter "s")
                                     AExpr (aBefore "serving")
                                     AExpr (aAfter "serving") ]] }, 
                  Normal)) ] }

/// The CFG for the ticket lock unlock method.
let ticketLockUnlockGraph : Graph =
    { Name = "unlock"
      Contents =
          Map.ofList
              [ ("unlock_V0",
                 (Mandatory <|
                  Multiset.singleton
                          (gfunc BTrue "holdLock" [] ),
                  Set.singleton
                      { Name = "unlock_C0"
                        Dest = "unlock_V1"
                        Command =
                            [ func "!I++"
                                   [ AExpr (aBefore "serving")
                                     AExpr (aAfter "serving") ]] },
                  Set.empty,
                  Entry))
                ("unlock_V1",
                 (Mandatory <| Multiset.empty,
                  Set.empty,
                  Set.singleton
                      { Name = "unlock_C0"
                        Src = "unlock_V0"
                        Command =
                            [ func "!I++"
                                   [ AExpr (aBefore "serving")
                                     AExpr (aAfter "serving") ]] }, 
                   Exit)) ] }
