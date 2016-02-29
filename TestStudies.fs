/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Axiom
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

/// The axioms of the ticketed lock.
let ticketLockAxioms = []
(*    
    [ { Pre = Multiset.empty()
        Post = 
           Multiset.ofList [ CFunc.Func { Name = "holdTick"
                                          Params = [ AExpr (AConst (Unmarked "t")) ] } ]
        Cmd = Prim (func "!ILoad++" ["t" |> aBefore |> AExpr; "t" |> aAfter |> AExpr
                                     "ticket" |> aBefore |> AExpr; "ticket" |> aAfter |> AExpr]) }
      { Pre = 
           Multiset.ofList [ CFunc.Func { Name = "holdTick"
                                          Params = [ AExpr (AConst (Unmarked "t")) ] } ]
        Post = 
           Multiset.ofList [ CFunc.Func { Name = "holdLock"
                                          Params = [] } ]
        Cmd = PartCmd.While(true, BNot(BEq(AExpr (AConst (Unmarked "s")), AExpr (AConst (Unmarked "t")))), 
                            { Pre = 
                                  Multiset.ofList [ CFunc.Func { Name = "holdTick"
                                                                 Params = [ AExpr (AConst (Unmarked "t")) ] } ]
                              Post = 
                                  Multiset.ofList 
                                      [ CFunc.ITE
                                            (BEq(AExpr (AConst (Unmarked "s")), AExpr (AConst (Unmarked "t"))), 
                                             Multiset.ofList [ CFunc.Func { Name = "holdLock"
                                                                            Params = [] } ], 
                                             Multiset.ofList [ CFunc.Func { Name = "holdTick"
                                                                            Params = [ AExpr (AConst (Unmarked "t")) ] } ]) ]
                              Cmd = 
                                  [ { Pre = 
                                          Multiset.ofList [ CFunc.Func { Name = "holdTick"
                                                                         Params = [ AExpr (AConst (Unmarked "t")) ] } ]
                                      Post = 
                                          Multiset.ofList 
                                              [ CFunc.ITE
                                                    (BEq(AExpr (AConst (Unmarked "s")), AExpr (AConst (Unmarked "t"))), 
                                                     Multiset.ofList [ CFunc.Func { Name = "holdLock"
                                                                                    Params = [] } ], 
                                                     Multiset.ofList [ CFunc.Func { Name = "holdTick"
                                                                                    Params = [ AExpr (AConst (Unmarked "t")) ] } ]) ]
                                      Cmd = Prim (func "!ILoad" ["s" |> aBefore |> AExpr; "s" |> aAfter |> AExpr
                                                                 "serving" |> aBefore |> AExpr; "serving" |> aAfter |> AExpr]) } ] }) }
      { Pre = 
            Multiset.ofList [ CFunc.Func { Name = "holdLock"
                                           Params = [] } ]
        Post = Multiset.empty()
        Cmd = Prim(func "!I++" ["serving" |> aBefore |> AExpr; "serving" |> aAfter |> AExpr]) } ] *)

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
      Axioms = ticketLockAxioms
      ViewDefs = ticketLockViewDefs
      Semantics = Starling.Lang.Modeller.coreSemantics }
