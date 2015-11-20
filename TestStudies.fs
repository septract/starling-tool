/// Case studies for unit testing.
module Starling.Tests.Studies

open Starling
open Starling.AST
open Starling.Collator

/// The raw form of the ticketed lock.

/// The parsed form of the ticketed lock.

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
          [ { Name = "lock"
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
                                                                          LVIdent "t",
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
                        ]}}
            { Name = "unlock"
              Params = []
              Body =
                  { Pre = Func ("holdLock", [])
                    Contents =
                        [ { Command = Atomic (Postfix (LVIdent "serving", Increment))
                            Post = Unit
                          }
                        ]}}
          ]
    }


