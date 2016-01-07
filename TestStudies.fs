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
                    Post = Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]} }
                  { Command = 
                        DoWhile
                            ({ Pre = Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]}
                               Contents = 
                                   [ { Command = Atomic(Fetch(LVIdent "s", LV(LVIdent "serving"), Direct))
                                       Post = 
                                           IfView
                                               (Bop(Eq, LV(LVIdent "s"), LV(LVIdent "t")), Func {Name = "holdLock"; Params = []}, 
                                                Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]}) } ] }, 
                             Bop(Neq, LV(LVIdent "s"), LV(LVIdent "t")))
                    Post = Func { Name = "holdLock"; Params = []} } ] } }

/// The correct parsing of the ticketed lock's unlock method.
let ticketLockUnlockMethodAST = 
    { Signature = {Name = "unlock"; Params = []}
      Body = 
          { Pre = Func {Name = "holdLock"; Params = []}
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
      Constraint { CView = ViewDef.Func {Name = "holdTick"; Params = [ "t" ]}
                   CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")) }
      Constraint { CView = ViewDef.Func {Name = "holdLock"; Params = []}
                   CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func {Name = "holdTick"; Params = [ "t" ]})
                   CExpression = Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func {Name = "holdTick"; Params = [ "ta" ]}, ViewDef.Func { Name = "holdTick"; Params = [ "tb" ]})
                   CExpression = Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")) }
      Constraint { CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func { Name = "holdLock"; Params = []})
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
              CView = ViewDef.Func {Name = "holdTick"; Params = [ "t" ]}
              CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "t")) }
            { // constraint holdLock() => ticket > serving;
              CView = ViewDef.Func {Name = "holdLock"; Params = []}
              CExpression = Bop(Gt, LV(LVIdent "ticket"), LV(LVIdent "serving")) }
            { // constraint holdLock() * holdTick(t) => serving != t;
              CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func {Name = "holdTick"; Params = [ "t" ]})
              CExpression = Bop(Neq, LV(LVIdent "serving"), LV(LVIdent "t")) }
            { // constraint holdLock() * holdLock() => false;
              CView = ViewDef.Join(ViewDef.Func {Name = "holdTick"; Params = [ "ta" ]}, ViewDef.Func {Name = "holdTick"; Params = [ "tb" ]})
              CExpression = Bop(Neq, LV(LVIdent "ta"), LV(LVIdent "tb")) }
            { CView = ViewDef.Join(ViewDef.Func {Name = "holdLock"; Params = []}, ViewDef.Func {Name = "holdLock"; Params = []})
              CExpression = False } ]
      Methods = [ ticketLockLockMethodAST; ticketLockUnlockMethodAST ] }

/// The axioms of the ticketed lock.
let ticketLockAxioms (ctx : Z3.Context) = 
    [ PAAxiom { Conditions = 
                    { Pre = Multiset.empty()
                      Post = 
                          Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                            Params = [ ctx.MkIntConst "t" ] } ] }
                Inner = IntLoad(Some(LVIdent "t"), LVIdent "ticket", Increment) }
      PAWhile(true, ctx.MkNot(ctx.MkEq(ctx.MkIntConst "s", ctx.MkIntConst "t")), 
              { Pre = 
                    Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                      Params = [ ctx.MkIntConst "t" ] } ]
                Post = 
                    Multiset.ofList [ CondView.Func { Name = "holdLock"
                                                      Params = [] } ] }, 
              { Conditions = 
                    { Pre = 
                          Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                            Params = [ ctx.MkIntConst "t" ] } ]
                      Post = 
                          Multiset.ofList 
                              [ ITE(ctx.MkEq(ctx.MkIntConst "s", ctx.MkIntConst "t"), 
                                         Multiset.ofList [ CondView.Func { Name = "holdLock"
                                                                           Params = [] } ], 
                                         Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                                           Params = [ ctx.MkIntConst "t" ] } ]) ] }
                Inner = 
                    [ PAAxiom { Conditions = 
                                    { Pre = 
                                          Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                                            Params = [ ctx.MkIntConst "t" ] } ]
                                      Post = 
                                          Multiset.ofList 
                                              [ ITE
                                                    (ctx.MkEq(ctx.MkIntConst "s", ctx.MkIntConst "t"), 
                                                     Multiset.ofList [ CondView.Func { Name = "holdLock"
                                                                                       Params = [] } ], 
                                                     Multiset.ofList [ CondView.Func { Name = "holdTick"
                                                                                       Params = [ ctx.MkIntConst "t" ] } ]) ] }
                                Inner = IntLoad(Some(LVIdent "s"), LVIdent "serving", Direct) } ] })
      PAAxiom { Conditions = 
                    { Pre = 
                          Multiset.ofList [ CondView.Func { Name = "holdLock"
                                                            Params = [] } ]
                      Post = Multiset.empty() }
                Inner = IntLoad(None, LVIdent "serving", Increment) } ]

/// The model of a ticketed lock method.
let ticketLockModel = 
    { VProtos = 
          Map.ofList [ ("holdTick", [ (Type.Int, "t") ])
                       ("holdLock", []) ]
      Globals = 
          Map.ofList [ ("serving", Int)
                       ("ticket", Int) ]
      Locals = 
          Map.ofList [ ("s", Int)
                       ("t", Int) ]
      Axioms = ticketLockAxioms
      DefViews = 
          [ { CViews = Multiset.empty()
              CExpr = ctx.MkGe(ctx.MkIntConst "ticket", ctx.MkIntConst "serving") }
            { CViews = 
                  Multiset.ofList [ { Name = "holdTick"
                                      Params = [ (Type.Int, "t") ] } ]
              CExpr = ctx.MkGt(ctx.MkIntConst "ticket", ctx.MkIntConst "t") }
            { CViews = 
                  Multiset.ofList [ { Name = "holdLock"
                                      Params = [] } ]
              CExpr = ctx.MkGt(ctx.MkIntConst "ticket", ctx.MkIntConst "serving") }
            { CViews = 
                  Multiset.ofList [ { Name = "holdLock"
                                      Params = [] }
                                    { Name = "holdTick"
                                      Params = [ (Type.Int, "t") ] } ]
              CExpr = ctx.MkNot(ctx.MkEq(ctx.MkIntConst "serving", ctx.MkIntConst "t")) }
            { CViews = 
                  Multiset.ofList [ { Name = "holdTick"
                                      Params = [ (Type.Int, "ta") ] }
                                    { Name = "holdTick"
                                      Params = [ (Type.Int, "tb") ] } ]
              CExpr = ctx.MkNot(ctx.MkEq(ctx.MkIntConst "ta", ctx.MkIntConst "tb")) }
            { CViews = 
                  Multiset.ofList [ { Name = "holdLock"
                                      Params = [] }
                                    { Name = "holdLock"
                                      Params = [] } ]
              CExpr = BFalse } ] }
