/// Case studies for unit testing.
module Starling.Tests.Studies

open Microsoft
open Starling
open Starling.Collections
open Starling.Var
open Starling.Model
open Starling.Lang.AST
open Starling.Lang.Collator

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

global int ticket;
global int serving;
local int t;
local int s;

method lock() {
  {| emp |}
    <t = ticket++>;
  {| holdTick(t) |}
    do {
      {| holdTick(t) |}
        <s = serving>;
      {| if s == t then holdLock else holdTick(t) |}
    } while (s != t);
  {| holdLock |}
}

method unlock() {
  {| holdLock() |}
    <serving++>;
  {| emp |}
}
"""

/// The correct parsing of the ticketed lock's lock method.
let ticketLockLockMethodAST = 
    { Name = "lock"
      Params = []
      Body = 
          { Pre = Unit
            Contents = 
                [ { Command = Atomic(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment))
                    Post = Func("holdTick", [ LV(LVIdent "t") ]) }
                  { Command = 
                        DoWhile
                            ({ Pre = Func("holdTick", [ LV(LVIdent "t") ])
                               Contents = 
                                   [ { Command = Atomic(Fetch(LVIdent "s", LV(LVIdent "serving"), Direct))
                                       Post = 
                                           IfView
                                               (Bop(Eq, LV(LVIdent "s"), LV(LVIdent "t")), Func("holdLock", []), 
                                                Func("holdTick", [ LV(LVIdent "t") ])) } ] }, 
                             Bop(Neq, LV(LVIdent "s"), LV(LVIdent "t")))
                    Post = Func("holdLock", []) } ] } }

/// The correct parsing of the ticketed lock's unlock method.
let ticketLockUnlockMethodAST = 
    { Name = "unlock"
      Params = []
      Body = 
          { Pre = Func("holdLock", [])
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
                   CExpression = Bop(Ge, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
      Constraint { CView = ViewDef.Func("holdTick", [ "t" ])
                   CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")) }
      Constraint { CView = ViewDef.Func("holdLock", [])
                   CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func("holdLock", []), ViewDef.Func("holdTick", [ "t" ]))
                   CExpression = Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func("holdTick", [ "ta" ]), ViewDef.Func("holdTick", [ "tb" ]))
                   CExpression = Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func("holdLock", []), ViewDef.Func("holdLock", []))
                   CExpression = False }
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
      VProtos = 
          [ { Name = "holdTick"
              Params = [ (Type.Int, "t") ] }
            { Name = "holdLock"
              Params = [] } ]
      Constraints = 
          [ { // constraint emp => ticket >= serving;
              CView = ViewDef.Unit
              CExpression = Bop(Ge, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
            { // constraint holdTick(t) => ticket > t;
              CView = ViewDef.Func("holdTick", [ "t" ])
              CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")) }
            { // constraint holdLock() => ticket > serving;
              CView = ViewDef.Func("holdLock", [])
              CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
            { // constraint holdLock() * holdTick(t) => serving != t;
              CView = ViewDef.Join(ViewDef.Func("holdLock", []), ViewDef.Func("holdTick", [ "t" ]))
              CExpression = Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")) }
            { // constraint holdLock() * holdLock() => false;
              CView = ViewDef.Join(ViewDef.Func("holdTick", [ "ta" ]), ViewDef.Func("holdTick", [ "tb" ]))
              CExpression = Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")) }
            { CView = ViewDef.Join(ViewDef.Func("holdLock", []), ViewDef.Func("holdLock", []))
              CExpression = False } ]
      Methods = [ ticketLockLockMethodAST; ticketLockUnlockMethodAST ] }

/// The axioms of the ticketed lock.
let ticketLockAxioms (ctx : Z3.Context) = 
    [ PAAxiom { Conditions = 
                    { Pre = Multiset.empty()
                      Post = 
                          Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                            VParams = [ ctx.MkIntConst "t" ] } ] }
                Inner = IntLoad(Some(LVIdent "t"), LVIdent "ticket", Increment) }
      PAWhile(true, ctx.MkNot(ctx.MkEq(ctx.MkIntConst "s", ctx.MkIntConst "t")), 
              { Pre = 
                    Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                      VParams = [ ctx.MkIntConst "t" ] } ]
                Post = 
                    Multiset.ofList [ CondView.Func { VName = "holdLock"
                                                      VParams = [] } ] }, 
              { Conditions = 
                    { Pre = 
                          Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                            VParams = [ ctx.MkIntConst "t" ] } ]
                      Post = 
                          Multiset.ofList 
                              [ ITE(ctx.MkEq(ctx.MkIntConst "s", ctx.MkIntConst "t"), 
                                         Multiset.ofList [ CondView.Func { VName = "holdLock"
                                                                           VParams = [] } ], 
                                         Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                                           VParams = [ ctx.MkIntConst "t" ] } ]) ] }
                Inner = 
                    [ PAAxiom { Conditions = 
                                    { Pre = 
                                          Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                                            VParams = [ ctx.MkIntConst "t" ] } ]
                                      Post = 
                                          Multiset.ofList 
                                              [ ITE
                                                    (ctx.MkEq(ctx.MkIntConst "s", ctx.MkIntConst "t"), 
                                                     Multiset.ofList [ CondView.Func { VName = "holdLock"
                                                                                       VParams = [] } ], 
                                                     Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                                                       VParams = [ ctx.MkIntConst "t" ] } ]) ] }
                                Inner = IntLoad(Some(LVIdent "s"), LVIdent "serving", Direct) } ] })
      PAAxiom { Conditions = 
                    { Pre = 
                          Multiset.ofList [ CondView.Func { VName = "holdLock"
                                                            VParams = [] } ]
                      Post = Multiset.empty() }
                Inner = IntLoad(None, LVIdent "serving", Increment) } ]

/// The model of a ticketed lock method.
/// Takes an existing Z3 context.
let ticketLockModel ctx = 
    { Context = ctx
      VProtos = 
          Map.ofList [ ("holdTick", [ (Type.Int, "t") ])
                       ("holdLock", []) ]
      Globals = 
          Map.ofList [ ("serving", makeVar ctx Type.Int "serving")
                       ("ticket", makeVar ctx Type.Int "ticket") ]
      Locals = 
          Map.ofList [ ("s", makeVar ctx Type.Int "s")
                       ("t", makeVar ctx Type.Int "t") ]
      Axioms = ticketLockAxioms ctx
      DefViews = 
          [ { CViews = Multiset.empty()
              CZ3 = ctx.MkGe(ctx.MkIntConst "ticket", ctx.MkIntConst "serving") }
            { CViews = 
                  Multiset.ofList [ { VName = "holdTick"
                                      VParams = [ (Type.Int, "t") ] } ]
              CZ3 = ctx.MkGt(ctx.MkIntConst "ticket", ctx.MkIntConst "t") }
            { CViews = 
                  Multiset.ofList [ { VName = "holdLock"
                                      VParams = [] } ]
              CZ3 = ctx.MkGt(ctx.MkIntConst "ticket", ctx.MkIntConst "serving") }
            { CViews = 
                  Multiset.ofList [ { VName = "holdLock"
                                      VParams = [] }
                                    { VName = "holdTick"
                                      VParams = [ (Type.Int, "t") ] } ]
              CZ3 = ctx.MkNot(ctx.MkEq(ctx.MkIntConst "serving", ctx.MkIntConst "t")) }
            { CViews = 
                  Multiset.ofList [ { VName = "holdTick"
                                      VParams = [ (Type.Int, "ta") ] }
                                    { VName = "holdTick"
                                      VParams = [ (Type.Int, "tb") ] } ]
              CZ3 = ctx.MkNot(ctx.MkEq(ctx.MkIntConst "ta", ctx.MkIntConst "tb")) }
            { CViews = 
                  Multiset.ofList [ { VName = "holdLock"
                                      VParams = [] }
                                    { VName = "holdLock"
                                      VParams = [] } ]
              CZ3 = ctx.MkFalse() } ] }
