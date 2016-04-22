/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.Collections
open Starling.Core.TypeSystem
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
                  Params = [ Param.Int "t" ] }
      ViewProto { Name = "holdLock"
                  Params = [] }
      Constraint (Definite
                      (DView.Unit,
                       Bop(Ge, LV(LVIdent "ticket"), LV(LVIdent "serving"))))
      Constraint (Definite
                      (DView.Func {Name = "holdTick"; Params = [ "t" ]},
                       Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t"))))
      Constraint (Definite
                      (DView.Func {Name = "holdLock"; Params = []},
                       Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving"))))
      Constraint (Definite
                      (DView.Join
                           (DView.Func {Name = "holdLock"; Params = []},
                            DView.Func {Name = "holdTick"; Params = [ "t" ]}),
                       Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t"))))
      Constraint (Definite
                      (DView.Join
                           (DView.Func {Name = "holdTick"; Params = [ "ta" ]},
                            DView.Func { Name = "holdTick"; Params = [ "tb" ]}),
                       Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb"))))
      Constraint (Definite
                      (DView.Join
                           (DView.Func {Name = "holdLock"; Params = []},
                            DView.Func { Name = "holdLock"; Params = []}),
                       False))
      Global (VarDecl.Int "ticket")
      Global (VarDecl.Int "serving")
      Local (VarDecl.Int "t")
      Local (VarDecl.Int "s")
      Method ticketLockLockMethodAST
      Method ticketLockUnlockMethodAST ]

/// The collated form of the ticket lock.
let ticketLockCollated =
    { CollatedScript.Globals =
          [ (VarDecl.Int "ticket")
            (VarDecl.Int "serving") ]
      Locals =
          [ (VarDecl.Int "t")
            (VarDecl.Int "s") ]
      Search = None
      VProtos =
          [ { Name = "holdTick"
              Params = [ (Param.Int "t") ] }
            { Name = "holdLock"
              Params = [] } ]
      Constraints =
          [ // constraint emp -> ticket >= serving;
            Definite
                (DView.Unit,
                 Bop(Ge, LV(LVIdent "ticket"), LV(LVIdent "serving")))
            // constraint holdTick(t) -> ticket > t;
            Definite
                (DView.Func {Name = "holdTick"; Params = [ "t" ]},
                 Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")))
            // constraint holdLock() -> ticket > serving;
            Definite
                (DView.Func {Name = "holdLock"; Params = []},
                 Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")))
            // constraint holdLock() * holdTick(t) -> serving != t;
            Definite
                (DView.Join
                     (DView.Func {Name = "holdLock"; Params = []},
                      DView.Func {Name = "holdTick"; Params = [ "t" ]}),
                 Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")))
            // constraint holdTick(ta) * holdTick(tb) -> ta != tb;
            Definite
                (DView.Join
                    (DView.Func {Name = "holdTick"; Params = [ "ta" ]},
                     DView.Func {Name = "holdTick"; Params = [ "tb" ]}),
                 Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")))
            // constraint holdLock() * holdLock() -> false;
            Definite
                (DView.Join
                    (DView.Func {Name = "holdLock"; Params = []},
                     DView.Func {Name = "holdLock"; Params = []}),
                 False) ]
      Methods = [ ticketLockLockMethodAST; ticketLockUnlockMethodAST ] }

/// Shorthand for Multiset.singleton.
let sing = Multiset.singleton

/// The conditional holdLock view.
let holdLock =
    smvfunc "holdLock" [] |> Func

/// The conditional holdTick view.
let holdTick =
    smvfunc "holdTick" [SMExpr.Int (siUnmarked "t")] |> Func

/// The guarded holdLock view.
let gHoldLock cnd : SMGFunc = smgfunc cnd "holdLock" []

/// The guarded holdTick view.
let gHoldTick cnd : SMGFunc = smgfunc cnd "holdTick" [SMExpr.Int (siUnmarked "t")]

/// Produces the expression 's!before == t!before'.
let sIsT mark = iEq (AVar (Reg (mark "s"))) (AVar (Reg (mark "t")))

/// The ticket lock's lock method.
let ticketLockLock =
    { Signature = func "lock" []
      Body =
          { Pre = Mandatory <| Multiset.empty
            Contents =
                [ { Command =
                        smvfunc "!ILoad++"
                             [ SMExpr.Int (siBefore "t"); SMExpr.Int (siAfter "t")
                               SMExpr.Int (siBefore "ticket"); SMExpr.Int (siAfter "ticket") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| sing holdTick }
                  { Command =
                        While (isDo = true,
                               expr = BNot (sIsT Before),
                               inner =
                                   { Pre = Mandatory <| sing holdTick
                                     Contents =
                                         [ { Command =
                                                 smvfunc "!ILoad"
                                                      [ SMExpr.Int (siBefore "s"); SMExpr.Int (siAfter "s")
                                                        SMExpr.Int (siBefore "serving"); SMExpr.Int (siAfter "serving") ]
                                                 |> List.singleton |> Prim
                                             Post =
                                                 (sIsT MarkedVar.Unmarked,
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
                        smvfunc "!I++" [ SMExpr.Int (siBefore "serving"); SMExpr.Int (siAfter "serving") ]
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
                        smvfunc "!ILoad++"
                             [ SMExpr.Int (siBefore "t"); SMExpr.Int (siAfter "t")
                               SMExpr.Int (siBefore "ticket"); SMExpr.Int (siAfter "ticket") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| sing (gHoldTick BTrue) }
                  { Command =
                        While (isDo = true,
                               expr = BNot (sIsT Before),
                               inner =
                                   { Pre = Mandatory <| sing (gHoldTick BTrue)
                                     Contents =
                                         [ { Command =
                                                 smvfunc "!ILoad"
                                                      [ SMExpr.Int (siBefore "s"); SMExpr.Int (siAfter "s")
                                                        SMExpr.Int (siBefore "serving"); SMExpr.Int (siAfter "serving") ]
                                                 |> List.singleton |> Prim
                                             Post =
                                                 Mandatory <|
                                                 Multiset.ofFlatList
                                                     [ gHoldLock (sIsT MarkedVar.Unmarked)
                                                       gHoldTick (BNot (sIsT MarkedVar.Unmarked)) ] } ] } )
                    Post = Mandatory <| sing (gHoldLock BTrue) } ] } }

/// The ticket lock's unlock method, in guarded form.
let ticketLockGuardedUnlock : PMethod<ViewExpr<SMGView>> =
    { Signature = func "unlock" []
      Body =
          { Pre = Mandatory <| sing (gHoldLock BTrue)
            Contents =
                [ { Command =
                        smvfunc "!I++" [ Expr.Int (siBefore "serving"); Expr.Int (siAfter "serving") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| Multiset.empty } ] } }

/// The view definitions of the ticket lock model.
let ticketLockViewDefs =
    [ Definite
          ([],
           BGe(siUnmarked "ticket", siUnmarked "serving"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdTick"
                   Params = [ Param.Int "t" ] } ] |> Multiset.toFlatList,
           BGt(siUnmarked "ticket", siUnmarked "t"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] } ] |> Multiset.toFlatList,
           BGt(siUnmarked "ticket", siUnmarked "serving"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] }
                 { Name = "holdTick"
                   Params = [ Param.Int "t" ] } ] |> Multiset.toFlatList,
           BNot(iEq (siUnmarked "serving") (siUnmarked "t")))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdTick"
                   Params = [ Param.Int "ta" ] }
                 { Name = "holdTick"
                   Params = [ Param.Int "tb" ] } ] |> Multiset.toFlatList,
           BNot(iEq (siUnmarked "ta") (siUnmarked "tb")))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] }
                 { Name = "holdLock"
                   Params = [] } ] |> Multiset.toFlatList,
           BFalse) ]

/// The model of the ticket lock.
let ticketLockModel : UVModel<PMethod<ViewExpr<CView>>> =
    { Globals =
          Map.ofList [ ("serving", Type.Int ())
                       ("ticket", Type.Int ()) ]
      Locals =
          Map.ofList [ ("s", Type.Int ())
                       ("t", Type.Int ()) ]
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
                         [ gHoldLock (sIsT MarkedVar.Unmarked)
                           gHoldTick (BNot (sIsT MarkedVar.Unmarked)) ], Normal)) ]
      Edges =
          Map.ofList
              [ ("lock_C0",
                     edge "lock_V0"
                          [ func "!ILoad++"
                                 [ Typed.Int (siBefore "t")
                                   Typed.Int (siAfter "t")
                                   Typed.Int (siBefore "ticket")
                                   Typed.Int (siAfter "ticket") ]]
                          "lock_V1")
                ("lock_C1",
                     edge "lock_V3"
                          [ func "!ILoad"
                                 [ Typed.Int (siBefore "s")
                                   Typed.Int (siAfter "s")
                                   Typed.Int (siBefore "serving")
                                   Typed.Int (siAfter "serving") ]]
                          "lock_V4")
                ("lock_C2",
                     edge "lock_V4"
                          [ func "Assume"
                                 [ Typed.Bool
                                       (BNot (iEq (siBefore "s")
                                                  (siBefore "t"))) ]]
                          "lock_V3")
                ("lock_C3",
                     edge "lock_V4"
                          [ func "Assume"
                                 [ Typed.Bool
                                       (iEq (siBefore "s")
                                            (siBefore "t")) ]]
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
                         (smgfunc BTrue "holdLock" [] ), Entry))
                ("unlock_V1", (Mandatory <| Multiset.empty, Exit)) ]
      Edges =
           Map.ofList
              [ ("unlock_C0",
                     edge "unlock_V0"
                          [ smvfunc "!I++"
                                 [ Typed.Int (siBefore "serving")
                                   Typed.Int (siAfter "serving") ]]
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
                            [ smvfunc "!ILoad++"
                                   [ Typed.Int (siBefore "t")
                                     Typed.Int (siAfter "t")
                                     Typed.Int (siBefore "ticket")
                                     Typed.Int (siAfter "ticket") ]] },
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
                            [ smvfunc "!ILoad++"
                                   [ Typed.Int (siBefore "t")
                                     Typed.Int (siAfter "t")
                                     Typed.Int (siBefore "ticket")
                                     Typed.Int (siAfter "ticket") ]] },
                  Normal ))
                ("lock_V2",
                 (Mandatory <| sing (gHoldLock BTrue),
                  Set.empty,
                  Set.singleton
                      { Name = "lock_C3"
                        Src = "lock_V4"
                        Command =
                            [ smvfunc "Assume"
                                   [ Typed.Bool
                                         (iEq (siBefore "s")
                                              (siBefore "t")) ]] }, 
                   Exit))
                ("lock_V3",
                 (Mandatory <| sing (gHoldTick BTrue),
                  Set.singleton
                      { Name = "lock_C1"
                        Dest = "lock_V4"
                        Command =
                            [ smvfunc "!ILoad"
                                   [ Typed.Int (siBefore "s")
                                     Typed.Int (siAfter "s")
                                     Typed.Int (siBefore "serving")
                                     Typed.Int (siAfter "serving") ]] },
                  Set.ofList
                      [ { Name = "lock_C2"
                          Src = "lock_V4"
                          Command =
                              [ smvfunc "Assume"
                                     [ Typed.Bool
                                           (BNot (iEq (siBefore "s")
                                                      (siBefore "t"))) ]] }
                        { Name = "lock_C4"
                          Src = "lock_V1"
                          Command = [] } ],
                   Normal))
                ("lock_V4",
                 (Mandatory <|
                  Multiset.ofFlatList
                      [ gHoldLock (sIsT MarkedVar.Unmarked)
                        gHoldTick (BNot (sIsT MarkedVar.Unmarked)) ],
                  Set.ofList
                      [ { Name = "lock_C2"
                          Dest = "lock_V3"
                          Command =
                              [ smvfunc "Assume"
                                     [ Typed.Bool
                                           (BNot (iEq (siBefore "s")
                                                      (siBefore "t"))) ]] }
                        { Name = "lock_C3"
                          Dest = "lock_V2"
                          Command =
                              [ smvfunc "Assume"
                                     [ Typed.Bool
                                           (iEq (siBefore "s")
                                                (siBefore "t")) ]] } ],
                  Set.singleton
                      { Name = "lock_C1"
                        Src = "lock_V3"
                        Command =
                            [ smvfunc "!ILoad"
                                   [ Typed.Int (siBefore "s")
                                     Typed.Int (siAfter "s")
                                     Typed.Int (siBefore "serving")
                                     Typed.Int (siAfter "serving") ]] }, 
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
                            [ smvfunc "!I++"
                                   [ Typed.Int (siBefore "serving")
                                     Typed.Int (siAfter "serving") ]] },
                  Set.empty,
                  Entry))
                ("unlock_V1",
                 (Mandatory <| Multiset.empty,
                  Set.empty,
                  Set.singleton
                      { Name = "unlock_C0"
                        Src = "unlock_V0"
                        Command =
                            [ smvfunc "!I++"
                                   [ Typed.Int (siBefore "serving")
                                     Typed.Int (siAfter "serving") ]] }, 
                   Exit)) ] }
