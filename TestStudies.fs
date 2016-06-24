/// <summary>
///     Pre-processed case studies for unit testing.
/// </summary>
module Starling.Tests.Studies

open Starling
open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.Var
open Starling.Core.Model
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
    svfunc "holdLock" [] |> Func

/// The conditional holdTick view.
let holdTick =
    svfunc "holdTick" [SVExpr.Int (siVar "t")] |> Func

/// The guarded holdLock view.
let gHoldLock cnd : SVGFunc = svgfunc cnd "holdLock" []

/// The guarded holdTick view.
let gHoldTick cnd : SVGFunc = svgfunc cnd "holdTick" [SVExpr.Int (siVar "t")]

/// Produces the expression 's!before == t!before'.
let sIsT = iEq (siVar "s") (siVar "t")

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
                               expr = BNot sIsT,
                               inner =
                                   { Pre = Mandatory <| sing holdTick
                                     Contents =
                                         [ { Command =
                                                 smvfunc "!ILoad"
                                                      [ SMExpr.Int (siBefore "s"); SMExpr.Int (siAfter "s")
                                                        SMExpr.Int (siBefore "serving"); SMExpr.Int (siAfter "serving") ]
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
                               expr = BNot sIsT,
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
                                                     [ gHoldLock sIsT
                                                       gHoldTick (BNot sIsT) ] } ] } )
                    Post = Mandatory <| sing (gHoldLock BTrue) } ] } }

/// The ticket lock's unlock method, in guarded form.
let ticketLockGuardedUnlock : PMethod<ViewExpr<SVGView>> =
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
           BGe(siVar "ticket", siVar "serving"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdTick"
                   Params = [ Param.Int "t" ] } ] |> Multiset.toFlatList,
           BGt(siVar "ticket", siVar "t"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] } ] |> Multiset.toFlatList,
           BGt(siVar "ticket", siVar "serving"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] }
                 { Name = "holdTick"
                   Params = [ Param.Int "t" ] } ] |> Multiset.toFlatList,
           BNot(iEq (siVar "serving") (siVar "t")))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdTick"
                   Params = [ Param.Int "ta" ] }
                 { Name = "holdTick"
                   Params = [ Param.Int "tb" ] } ] |> Multiset.toFlatList,
           BNot(iEq (siVar "ta") (siVar "tb")))
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
