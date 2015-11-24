/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.AST
open Starling.Collator

/// The raw form of the ticketed lock.
let ticketLock = """
view holdTick(int t);
view holdLock();

constraint emp                       => ticket >= serving;
constraint holdTick(t)               => ticket > t;
constraint holdLock()                => ticket > serving;
constraint holdLock()  * holdTick(t) => serving != t;
constraint holdTick(t) * holdTick(t) => false;
constraint holdLock()  * holdLock()  => false;

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
                                         Post = IfView (EqExp (LVExp (LVIdent "s"),
                                                               LVExp (LVIdent "t")),
                                                        Func ("holdLock", []),
                                                        Func ("holdTick", [LVExp (LVIdent "t")])) } ]
                               },
                               EqExp (LVExp (LVIdent "s"),
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
                    CExpression = GeExp (LVExp (LVIdent "ticket"),
                                         LVExp (LVIdent "serving")) }
      SConstraint { CView = DFunc ("holdTick", ["t"])
                    CExpression = GtExp (LVExp (LVIdent "ticket"),
                                         LVExp (LVIdent "t")) }
      SConstraint { CView = DFunc ("holdLock", [])
                    CExpression = GtExp (LVExp (LVIdent "ticket"),
                                         LVExp (LVIdent "serving")) }
      SConstraint { CView = DJoin (DFunc ("holdLock", []),
                                   DFunc ("holdTick", ["t"]))
                    CExpression = NeqExp (LVExp (LVIdent "serving"),
                                          LVExp (LVIdent "t")) }
      SConstraint { CView = DJoin (DFunc ("holdTick", ["t"]),
                                   DFunc ("holdTick", ["t"]))
                    CExpression = FalseExp }
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
            CExpression = GeExp (LVExp (LVIdent "ticket"),
                                 LVExp (LVIdent "serving")) }
          // constraint holdTick(t) => ticket > t;
          { CView = DFunc ("holdTick", ["t"])
            CExpression = GtExp (LVExp (LVIdent "ticket"),
                                 LVExp (LVIdent "t")) }
          // constraint holdLock() => ticket > serving;
          { CView = DFunc ("holdLock", [])
            CExpression = GtExp (LVExp (LVIdent "ticket"),
                                 LVExp (LVIdent "serving")) }
          // constraint holdLock() * holdTick(t) => serving != t;
          { CView = DJoin (DFunc ("holdLock", []),
                           DFunc ("holdTick", ["t"]))
            CExpression = NeqExp (LVExp (LVIdent "serving"),
                                  LVExp (LVIdent "t")) }
          // constraint holdLock() * holdLock() => false;
          { CView = DJoin (DFunc ("holdTick", ["t"]),
                           DFunc ("holdTick", ["t"]))
            CExpression = FalseExp }
          { CView = DJoin (DFunc ("holdLock", []),
                           DFunc ("holdLock", []))
            CExpression = FalseExp } ]
      CMethods =
          [ ticketLockLockMethodAST
            ticketLockUnlockMethodAST ] }


