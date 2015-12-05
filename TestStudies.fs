/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.Var
open Starling.AST
open Starling.Model
open Starling.Collator

/// The raw form of the ticketed lock.
let ticketLock = """
view holdTick(int t);
view holdLock();

constraint emp                         => ticket >= serving;
constraint holdTick(t)                 => ticket > t;
constraint holdLock()                  => ticket > serving;
constraint holdLock()   * holdTick(t)  => serving != t;
constraint holdTick(ta) * holdTick(tb) => ta != tb;
constraint holdLock()   * holdLock()   => false;

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
    } while (s == t)
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
                [ { Command = Atomic (Fetch (LVIdent "t",
                                             LVIdent "ticket",
                                             Increment))
                    Post = Func ("holdTick", [LVExp (LVIdent "t")])
                  }
                  { Command =
                      DoWhile ({ Pre = Func ("holdTick", [LVExp (LVIdent "t")])
                                 Contents =
                                     [ { Command = Atomic (Fetch (LVIdent "s",
                                                                  LVIdent "serving",
                                                                  Direct))
                                         Post = IfView (BopExp (Eq,
                                                                LVExp (LVIdent "s"),
                                                                LVExp (LVIdent "t")),
                                                        Func ("holdLock", []),
                                                        Func ("holdTick", [LVExp (LVIdent "t")])) } ]
                               },
                               BopExp (Eq,
                                       LVExp (LVIdent "s"),
                                       LVExp (LVIdent "t")))

                    Post = Func ("holdLock", [])
                  }
                ] }}

/// The correct parsing of the ticketed lock's unlock method.
let ticketLockUnlockMethodAST =
    { Name = "unlock"
      Params = []
      Body =
          { Pre = Func ("holdLock", [])
            Contents =
                [ { Command = Atomic (Postfix (LVIdent "serving", Increment))
                    Post = Unit
                  }
                ]}}

/// The parsed form of the ticketed lock.
let ticketLockParsed =
    [ SViewProto { VPName = "holdTick" ; VPPars = [ (Int, "t") ] }
      SViewProto { VPName = "holdLock" ; VPPars = [] }
      SConstraint { CView = DUnit
                    CExpression = BopExp (Ge,
                                          LVExp (LVIdent "ticket"),
                                          LVExp (LVIdent "serving")) }
      SConstraint { CView = DFunc ("holdTick", ["t"])
                    CExpression = BopExp (Gt,
                                          LVExp (LVIdent "ticket"),
                                          LVExp (LVIdent "t")) }
      SConstraint { CView = DFunc ("holdLock", [])
                    CExpression = BopExp (Gt,
                                          LVExp (LVIdent "ticket"),
                                          LVExp (LVIdent "serving")) }
      SConstraint { CView = DJoin (DFunc ("holdLock", []),
                                   DFunc ("holdTick", ["t"]))
                    CExpression = BopExp (Neq,
                                          LVExp (LVIdent "serving"),
                                          LVExp (LVIdent "t")) }
      SConstraint { CView = DJoin (DFunc ("holdTick", ["ta"]),
                                   DFunc ("holdTick", ["tb"]))
                    CExpression = BopExp (Neq,
                                          LVExp (LVIdent "ta"),
                                          LVExp (LVIdent "tb")) }
      SConstraint { CView = DJoin (DFunc ("holdLock", []),
                                   DFunc ("holdLock", []))
                    CExpression = FalseExp }
      SGlobal (Int, "ticket")
      SGlobal (Int, "serving")
      SLocal (Int, "t")
      SLocal (Int, "s")
      SMethod ticketLockLockMethodAST
      SMethod ticketLockUnlockMethodAST]


/// The collated form of the ticketed lock.
let ticketLockCollated =
    { CGlobals =
        [ (Int, "ticket")
          (Int, "serving") ]
      CLocals =
        [ (Int, "t")
          (Int, "s") ]
      CVProtos =
        [ { VPName = "holdTick" ; VPPars = [ (Int, "t") ] }
          { VPName = "holdLock" ; VPPars = [] } ]
      CConstraints =
        [ // constraint emp => ticket >= serving;
          { CView = DUnit
            CExpression = BopExp (Ge,
                                  LVExp (LVIdent "ticket"),
                                  LVExp (LVIdent "serving")) }
          // constraint holdTick(t) => ticket > t;
          { CView = DFunc ("holdTick", ["t"])
            CExpression = BopExp (Gt,
                                  LVExp (LVIdent "ticket"),
                                  LVExp (LVIdent "t")) }
          // constraint holdLock() => ticket > serving;
          { CView = DFunc ("holdLock", [])
            CExpression = BopExp (Gt,
                                  LVExp (LVIdent "ticket"),
                                  LVExp (LVIdent "serving")) }
          // constraint holdLock() * holdTick(t) => serving != t;
          { CView = DJoin (DFunc ("holdLock", []),
                           DFunc ("holdTick", ["t"]))
            CExpression = BopExp (Neq,
                                  LVExp (LVIdent "serving"),
                                  LVExp (LVIdent "t")) }
          // constraint holdLock() * holdLock() => false;
          { CView = DJoin (DFunc ("holdTick", ["ta"]),
                           DFunc ("holdTick", ["tb"]))
            CExpression = BopExp (Neq,
                                  LVExp (LVIdent "ta"),
                                  LVExp (LVIdent "tb")) }
          { CView = DJoin (DFunc ("holdLock", []),
                           DFunc ("holdLock", []))
            CExpression = FalseExp } ]
      CMethods =
          [ ticketLockLockMethodAST
            ticketLockUnlockMethodAST ] }

/// The model of a ticketed lock method.
/// Takes an existing Z3 context.
let ticketLockModel ctx =
    {Context = ctx
     VProtos =
         Map.ofList [ ("holdTick", [ (Int, "t") ] )
                      ("holdLock", [] ) ]
     Globals =
         Map.ofList [ ("serving",
                       IntVar {VarExpr = ctx.MkIntConst "serving"
                               VarPreExpr = ctx.MkIntConst "serving!before"
                               VarPostExpr = ctx.MkIntConst "serving!after"
                               VarFrameExpr = ctx.MkIntConst "serving!r"} )
                      ("ticket",
                       IntVar {VarExpr = ctx.MkIntConst "ticket"
                               VarPreExpr = ctx.MkIntConst "ticket!before"
                               VarPostExpr = ctx.MkIntConst "ticket!after"
                               VarFrameExpr = ctx.MkIntConst "ticket!r"} ) ]
     Locals =
         Map.ofList [ ("s",
                       IntVar {VarExpr = ctx.MkIntConst "s"
                               VarPreExpr = ctx.MkIntConst "s!before"
                               VarPostExpr = ctx.MkIntConst "s!after"
                               VarFrameExpr = ctx.MkIntConst "s!r"} )
                      ("t",
                       IntVar {VarExpr = ctx.MkIntConst "t"
                               VarPreExpr = ctx.MkIntConst "t!before"
                               VarPostExpr = ctx.MkIntConst "t!after"
                               VarFrameExpr = ctx.MkIntConst "t!r"} ) ]
     Axioms =
         [PAAxiom {Conditions = {Pre = []
                                 Post = [CSetView {VName = "holdTick";
                                                   VParams = [ctx.MkIntConst "t"]} ] }
                   Inner = ArithFetch (Some (LVIdent "t"),
                                       LVIdent "ticket",
                                       Increment) }
          PAWhile (true,
                   ctx.MkEq (ctx.MkIntConst "s",
                             ctx.MkIntConst "t"),
                   {Pre = [CSetView {VName = "holdTick"
                                     VParams = [ctx.MkIntConst "t"] } ]
                    Post = [CSetView {VName = "holdLock"
                                      VParams = [] } ] },
                   {Conditions = {Pre = [CSetView {VName = "holdTick"
                                                   VParams = [ctx.MkIntConst "t"] } ]
                                  Post = [CITEView (ctx.MkEq (ctx.MkIntConst "s",
                                                              ctx.MkIntConst "t"),
                                                    [CSetView {VName = "holdLock"
                                                               VParams = [] } ],
                                                    [CSetView {VName = "holdTick"
                                                               VParams = [ctx.MkIntConst "t"] } ] ) ] }
                    Inner =
                        [PAAxiom {Conditions = {Pre = [CSetView {VName = "holdTick"
                                                                 VParams = [ctx.MkIntConst "t"] } ]
                                                Post = [CITEView (ctx.MkEq (ctx.MkIntConst "s",
                                                                            ctx.MkIntConst "t"),
                                                                  [CSetView {VName = "holdLock"
                                                                             VParams = [] } ],
                                                                  [CSetView {VName = "holdTick"
                                                                             VParams = [ctx.MkIntConst "t"] } ] ) ] }
                                  Inner = ArithFetch (Some (LVIdent "s"),
                                                      LVIdent "serving",
                                                      Direct) } ] } )
          PAAxiom {Conditions = {Pre = [CSetView {VName = "holdLock"
                                                  VParams = [] } ]
                                 Post = [] }
                   Inner = ArithFetch (None,
                                       LVIdent "serving",Increment) } ]
     DefViews =
      [ {CViews = []
         CZ3 = ctx.MkGe (ctx.MkIntConst "ticket",
                         ctx.MkIntConst "serving") }
        {CViews = [ {VName = "holdTick"
                     VParams = [(Int, "t")] } ]
         CZ3 = ctx.MkGt (ctx.MkIntConst "ticket",
                         ctx.MkIntConst "t") }
        {CViews = [ {VName = "holdLock"
                     VParams = [] } ]
         CZ3 = ctx.MkGt (ctx.MkIntConst "ticket",
                         ctx.MkIntConst "serving") }
        {CViews = [ {VName = "holdLock"
                     VParams = [] }
                    {VName = "holdTick"
                     VParams = [(Int, "t")] } ]
         CZ3 = ctx.MkNot (ctx.MkEq (ctx.MkIntConst "serving",
                                    ctx.MkIntConst "t")) }
        {CViews = [ {VName = "holdTick"
                     VParams = [(Int, "ta")] }
                    {VName = "holdTick"
                     VParams = [(Int, "tb")] } ]
         CZ3 = ctx.MkNot (ctx.MkEq (ctx.MkIntConst "ta",
                                    ctx.MkIntConst "tb")) }
        {CViews = [ {VName = "holdLock"
                     VParams = [] }
                    {VName = "holdLock"
                     VParams = [] } ]
         CZ3 = ctx.MkFalse () } ] }
