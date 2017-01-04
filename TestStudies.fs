/// <summary>
///     Pre-processed case studies for unit testing.
/// </summary>
module Starling.Tests.Studies

open Starling
open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.Var
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.Modeller
open Starling.Lang.Guarder


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

let pos l c node =
    { Position = { StreamName = "Examples/Pass/ticketLock.cvf"
                   Line = l
                   Column = c }
      Node = node }

/// The correct parsing of the ticket lock's lock method.
let ticketLockLockMethodAST =
    { Signature = { Name = "lock"; Params = [] }
      Body =
        { Pre = Unmarked Unit;
          Contents =
            [ { Command =
                    pos 15L 5L <| Command'.Prim
                        { PreAssigns = []
                          Atomics =
                            [ pos 15L 6L <|
                              Fetch
                                (pos 15L 6L (Identifier "t"),
                                 pos 15L 10L (Identifier "ticket"),
                                 Increment) ]
                          PostAssigns = [] }
                Post =
                    Unmarked
                        (View.Func
                            { Name = "holdTick"
                              Params =
                                [ pos 16L 15L <| Identifier "t" ] })}
              { Command =
                    pos 17L 5L <| DoWhile
                        ({ Pre =
                            Unmarked
                                (View.Func
                                    { Name = "holdTick"
                                      Params =
                                        [ pos 18L 19L <| Identifier "t" ] })
                           Contents =
                            [ { Command =
                                    pos 19L 9L <| Command'.Prim
                                        { PreAssigns = []
                                          Atomics =
                                            [ pos 19L 10L <| Fetch
                                                (pos 19L 10L <| Identifier "s",
                                                 pos 19L 14L <| Identifier "serving",
                                                 Direct) ]
                                          PostAssigns = [] }
                                Post =
                                    Unmarked
                                        (View.If
                                            (pos 20L 15L <| BopExpr
                                                (Eq,
                                                 pos 20L 13L (Identifier "s"),
                                                 pos 20L 18L (Identifier "t")),
                                             View.Func { Name = "holdLock"; Params = [] },
                                             View.Func
                                               { Name = "holdTick"
                                                 Params =
                                                    [ pos 20L 50L (Identifier "t") ] }))}]},
                         pos 21L 16L <| BopExpr
                            (Neq,
                             pos 21L 14L (Identifier "s"),
                             pos 21L 19L (Identifier "t")))
                Post =
                    Unmarked (View.Func { Name = "holdLock"; Params = []})}]}}

/// The correct parsing of the ticket lock's unlock method.
let ticketLockUnlockMethodAST =
    {Signature = {Name = "unlock";
                    Params = [];};
       Body =
        {Pre = Unmarked (View.Func {Name = "holdLock";
                               Params = [];});
         Contents =
          [{Command =
             pos 30L 5L <| Command'.Prim
                 {PreAssigns = []
                  Atomics =
                    [ pos 30L 6L <| Postfix
                        (pos 30L 6L (Identifier "serving"),
                         Increment) ]
                  PostAssigns = [] }
            Post = Unmarked Unit;}];};};

let ticketLockConstraint01 =
    (ViewSignature.Unit,
     Some
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 38L;
                   Column = 50L;};
       Node =
        BopExpr
          (Ge,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                           Line = 38L;
                           Column = 43L;};
               Node = Identifier "ticket";},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 38L;
                        Column = 53L;};
            Node = Identifier "serving";});})

let ticketLockConstraint02 =
    (ViewSignature.Func {Name = "holdTick";
            Params = ["t"];},
     Some
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 41L;
                   Column = 50L;};
       Node =
        BopExpr
          (Gt,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                           Line = 41L;
                           Column = 43L;};
               Node = Identifier "ticket";},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 41L;
                        Column = 52L;};
            Node = Identifier "t";});})

let ticketLockConstraint03 =
    (ViewSignature.Func {Name = "holdLock";
            Params = [];},
     Some
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 42L;
                   Column = 50L;};
       Node =
        BopExpr
          (Neq,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 42L;
                            Column = 43L;};
                Node = Identifier "ticket";},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 42L;
                        Column = 53L;};
            Node = Identifier "serving";});})

let ticketLockConstraint04 =
    (ViewSignature.Join (ViewSignature.Func {Name = "holdLock";
                             Params = [];},
                 ViewSignature.Func {Name = "holdTick";
                             Params = ["t"];}),
     Some
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 45L;
                   Column = 51L;};
       Node =
        BopExpr
          (Neq,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 45L;
                            Column = 43L;};
                Node = Identifier "serving";},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 45L;
                        Column = 54L;};
            Node = Identifier "t";});})

let ticketLockConstraint05 =
    (ViewSignature.Join (ViewSignature.Func {Name = "holdTick";
                             Params = ["ta"];},
                 ViewSignature.Func {Name = "holdTick";
                             Params = ["tb"];}),
     Some
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 46L;
                   Column = 46L;};
       Node =
        BopExpr
          (Neq,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 46L;
                            Column = 43L;};
                Node = Identifier "ta";},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 46L;
                        Column = 49L;};
            Node = Identifier "tb";});})

let ticketLockConstraint06 =
    (ViewSignature.Join (ViewSignature.Func {Name = "holdLock";
                             Params = [];},
                 ViewSignature.Func {Name = "holdLock";
                             Params = [];}),
     Some
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 47L;
                   Column = 43L;};
       Node = False;})

/// The parsed form of the ticket lock.
let ticketLockParsed =
    [ { Position =
            { StreamName = "Examples/Pass/ticketLock.cvf"
              Line = 34L; Column = 1L }
        Node =
            ViewProtos
                [ NoIterator
                    ({ Name = "holdTick"
                       Params = [ { ParamType = TInt; ParamName = "t" } ] },
                     false) ] }
      { Position =
            { StreamName = "Examples/Pass/ticketLock.cvf"
              Line = 35L; Column = 1L }
        Node =
            ViewProtos
                [ NoIterator ({ Name = "holdLock"; Params = [] }, false) ] }
      { Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 38L;
                   Column = 1L;};
       Node =
        Constraint ticketLockConstraint01}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 41L;
                   Column = 1L;};
       Node =
        Constraint ticketLockConstraint02}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 42L;
                   Column = 1L;};
       Node =
        Constraint ticketLockConstraint03}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 45L;
                   Column = 1L;};
       Node =
        Constraint ticketLockConstraint04}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 46L;
                   Column = 1L;};
       Node =
        Constraint ticketLockConstraint05}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 47L;
                   Column = 1L;};
       Node =
        Constraint ticketLockConstraint06}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 5L
                   Column = 1L}
       Node = SharedVars { VarType = TInt; VarNames = ["ticket"] }}
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf"
                   Line = 6L
                   Column = 1L}
       Node = SharedVars { VarType = TInt; VarNames = ["serving"] }}
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf"
                   Line = 7L
                   Column = 1L}
       Node = ThreadVars { VarType = TInt; VarNames = ["t"] }}
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf"
                   Line = 8L
                   Column = 1L}
       Node = ThreadVars { VarType = TInt; VarNames = ["s"] }}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf"
                   Line = 13L
                   Column = 1L}
       Node = Method ticketLockLockMethodAST}

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf"
                   Line = 28L
                   Column = 1L}
       Node = Method ticketLockUnlockMethodAST}
       ]

/// The collated form of the ticket lock.
let ticketLockCollated =
    { Pragmata = []
      Typedefs = []
      CollatedScript.SharedVars =
          [ (TInt, "ticket")
            (TInt, "serving") ]
      ThreadVars =
          [ (TInt, "t")
            (TInt, "s") ]
      Search = None
      VProtos =
          [ NoIterator
                ({ Name = "holdTick"
                   Params = [ { ParamType = TInt; ParamName = "t" } ] }, false)
            NoIterator
                ({ Name = "holdLock"
                   Params = [] }, false) ]
      Constraints =
          [ // constraint emp -> ticket >= serving;
            ticketLockConstraint01
            // constraint holdTick(t) -> ticket > t;
            ticketLockConstraint02
            // constraint holdLock() -> ticket > serving;
            ticketLockConstraint03
            // constraint holdLock() * holdTick(t) -> serving != t;
            ticketLockConstraint04
            // constraint holdTick(ta) * holdTick(tb) -> ta != tb;
            ticketLockConstraint05
            // constraint holdLock() * holdLock() -> false;
            ticketLockConstraint06 ]
      Methods =
          Map.ofList
              [ ("lock", ticketLockLockMethodAST.Body)
                ("unlock", ticketLockUnlockMethodAST.Body) ] }

/// Shorthand for Multiset.singleton.
let sing = Multiset.singleton

/// The conditional holdLock view.
let holdLock =
    { Func = Func (svfunc "holdLock" [])
      Iterator = None }

/// The conditional holdTick view.
let holdTick =
    { Func = Func (svfunc "holdTick" [normalIntExpr (siVar "t")])
      Iterator = None }


let oneGFunc (cnd : BoolExpr<Sym<Var>>) (name : string)
  (ps : Expr<Sym<Var>> list)
  : IteratedGFunc<Sym<Var>> =
    iterated (svgfunc cnd name ps) (IInt 1L)

/// The guarded holdLock view.
let gHoldLock cnd : IteratedGFunc<Sym<Var>> =
    oneGFunc cnd "holdLock" []

/// The guarded holdTick view.
let gHoldTick cnd : IteratedGFunc<Sym<Var>> =
    oneGFunc cnd "holdTick" [normalIntExpr (siVar "t")]

/// Produces the expression 's!before == t!before'.
let sIsT = iEq (siVar "s") (siVar "t")

/// The ticket lock's lock method.
let ticketLockLock =
    { Signature = func "lock" []
      Body =
        { Pre = Mandatory <| Multiset.empty
          Contents =
            [ { Command =
                    command "!ILoad++"
                        [ normalIntExpr (siVar "t"); normalIntExpr (siVar "ticket") ]
                        [ normalIntExpr (siVar "ticket") ]
                    |> List.singleton |> Prim
                Post = Mandatory <| sing holdTick }
              { Command =
                    While (isDo = true,
                           expr = BNot sIsT,
                           inner =
                               { Pre = Mandatory <| sing holdTick
                                 Contents =
                                     [ { Command =
                                             command "!ILoad" [ normalIntExpr (siVar "s") ]
                                                  [ normalIntExpr (siVar "serving") ]
                                             |> List.singleton |> Prim
                                         Post =
                                            { Func =
                                                CFunc.ITE
                                                 (sIsT,
                                                  sing holdLock,
                                                  sing holdTick)
                                              Iterator = None }
                                             |> Multiset.singleton
                                             |> Mandatory } ] } )
                Post = Mandatory <| sing holdLock } ] } }

/// The ticket lock's unlock method.
let ticketLockUnlock =
    { Signature = func "unlock" []
      Body =
          { Pre = Mandatory <| sing holdLock
            // constraint holdTick(ta) * holdTick(tb) -> ta != tb;
            Contents =
                [ { Command =
                        command "!I++" [ normalIntExpr (siVar "serving") ] [ normalIntExpr (siVar "serving") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| Multiset.empty }]}}

/// The methods of the ticket lock.
let ticketLockMethods =
    [ ("lock", ticketLockLock.Body)
      ("unlock", ticketLockUnlock.Body) ] |> Map.ofList


/// The ticket lock's lock method, in guarded form.
let ticketLockGuardedLock : GuarderBlock =
      { Pre = Mandatory <| Multiset.empty
        Contents =
            [ { Command =
                    command "!ILoad++"
                         [ normalIntExpr (siVar "t"); normalIntExpr (siVar "ticket") ]
                         [ normalIntExpr (siVar "t");
                           normalIntExpr (siVar "ticket"); ]
                    |> List.singleton |> Prim
                Post = Mandatory <| sing (gHoldTick BTrue) }
              { Command =
                    While (isDo = true,
                           expr = BNot sIsT,
                           inner =
                               { Pre = Mandatory <| sing (gHoldTick BTrue)
                                 Contents =
                                     [ { Command =
                                             command "!ILoad"
                                                  [ normalIntExpr (siVar "s") ]
                                                  [ normalIntExpr (siVar "serving"); ]
                                             |> List.singleton |> Prim
                                         Post =
                                             Mandatory <|
                                             Multiset.ofFlatList
                                                 [ gHoldLock sIsT
                                                   gHoldTick (BNot sIsT) ] } ] } )
                Post = Mandatory <| sing (gHoldLock BTrue) } ] } 

/// The ticket lock's unlock method, in guarded form.
let ticketLockGuardedUnlock : GuarderBlock =
      { Pre = Mandatory <| sing (gHoldLock BTrue)
        Contents =
            [ { Command =
                    command "!I++" [ normalIntExpr (siVar "serving") ] [ normalIntExpr (siVar "serving") ]
                    |> List.singleton |> Prim
                Post = Mandatory <| Multiset.empty } ] }

/// The view definitions of the ticket lock model.
let ticketLockViewDefs =
    [([],
      Some <| BGe(normalInt (siVar "ticket"), normalInt (siVar "serving")))
     ([ { Func = { Name = "holdTick"; Params = [ TypedVar.Int (normalRec, "t") ] }
          Iterator = None } ],
      Some <| BGt(normalInt (siVar "ticket"), normalInt (siVar "t")))
     ([ { Func = { Name = "holdLock"; Params = [] }
          Iterator = None } ],
      Some <| BNot (iEq (siVar "ticket") (siVar "serving")))
     ([ { Func = { Name = "holdLock"; Params = [] }
          Iterator = None }
        { Func = { Name = "holdTick"; Params = [ TypedVar.Int (normalRec, "t") ] }
          Iterator = None } ],
      Some <| BNot(iEq (siVar "serving") (siVar "t")))
     ([ { Func = { Name = "holdTick"; Params = [ TypedVar.Int (normalRec, "ta") ] }
          Iterator = None }
        { Func = { Name = "holdTick"; Params = [ TypedVar.Int (normalRec, "tb") ] }
          Iterator = None } ],
      Some <| BNot(iEq (siVar "ta") (siVar "tb")))
     ([ { Func = { Name = "holdLock"; Params = [] }
          Iterator = None }
        { Func = { Name = "holdLock"; Params = [] }
          Iterator = None } ],
      Some BFalse) ]

let ticketLockViewProtos : FuncDefiner<ProtoInfo> =
    FuncDefiner.ofSeq
        [ ({ Name = "holdTick"; Params = [ TypedVar.Int (normalRec, "t") ] },
           { IsIterated = false; IsAnonymous = false })
          ({ Name = "holdLock"; Params = [] },
           { IsIterated = false; IsAnonymous = false }) ]

/// The model of the ticket lock.
let ticketLockModel : Model<ModellerBlock, ViewDefiner<BoolExpr<Sym<Var>> option>> =
    { Pragmata = []
      SharedVars =
          Map.ofList [ ("serving", Type.Int (normalRec, ()))
                       ("ticket", Type.Int (normalRec, ())) ]
      ThreadVars =
          Map.ofList [ ("s", Type.Int (normalRec, ()))
                       ("t", Type.Int (normalRec, ())) ]
      Axioms = ticketLockMethods
      ViewDefs = ticketLockViewDefs
      ViewProtos = ticketLockViewProtos
      Semantics = Starling.Lang.Modeller.coreSemantics
      DeferredChecks = [] }
