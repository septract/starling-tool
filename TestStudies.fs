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

/// The correct parsing of the ticket lock's lock method.
let ticketLockLockMethodAST =
    {Signature = {Name = "lock";
                  Params = [];};
           Body =
            {Pre = Unmarked Unit;
             Contents =
              [{Command =
                 {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                              Line = 15L;
                              Column = 5L;};
                  Node =
                   Command'.Prim
                     {PreAssigns = [];
                      Atomics =
                       [{Position =
                          {StreamName = "Examples/Pass/ticketLock.cvf";
                           Line = 15L;
                           Column = 6L;};
                         Node =
                          Fetch
                            (LVIdent "t",
                             {Position =
                               {StreamName = "Examples/Pass/ticketLock.cvf";
                                Line = 15L;
                                Column = 10L;};
                              Node = LV (LVIdent "ticket");},Increment);}];
                      PostAssigns = [];};};
                Post =
                 Unmarked
                   (View.Func
                      {Name = "holdTick";
                       Params =
                        [{Position =
                           {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 16L;
                            Column = 15L;};
                          Node = LV (LVIdent "t");}];});};
               {Command =
                 {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                              Line = 17L;
                              Column = 5L;};
                  Node =
                   DoWhile
                     ({Pre =
                        Unmarked
                          (View.Func
                             {Name = "holdTick";
                              Params =
                               [{Position =
                                  {StreamName = "Examples/Pass/ticketLock.cvf";
                                   Line = 18L;
                                   Column = 19L;};
                                 Node = LV (LVIdent "t");}];});
                       Contents =
                        [{Command =
                           {Position =
                             {StreamName = "Examples/Pass/ticketLock.cvf";
                              Line = 19L;
                              Column = 9L;};
                            Node =
                             Command'.Prim
                               {PreAssigns = [];
                                Atomics =
                                 [{Position =
                                    {StreamName =
                                      "Examples/Pass/ticketLock.cvf";
                                     Line = 19L;
                                     Column = 10L;};
                                   Node =
                                    Fetch
                                      (LVIdent "s",
                                       {Position =
                                         {StreamName =
                                           "Examples/Pass/ticketLock.cvf";
                                          Line = 19L;
                                          Column = 14L;};
                                        Node = LV (LVIdent "serving");},Direct);}];
                                PostAssigns = [];};};
                          Post =
                           Unmarked
                             (View.If
                                ({Position =
                                   {StreamName = "Examples/Pass/ticketLock.cvf";
                                    Line = 20L;
                                    Column = 15L;};
                                  Node =
                                   BopExpr
                                     (Eq,
                                      {Position =
                                        {StreamName =
                                          "Examples/Pass/ticketLock.cvf";
                                         Line = 20L;
                                         Column = 13L;};
                                       Node = LV (LVIdent "s");},
                                      {Position =
                                        {StreamName =
                                          "Examples/Pass/ticketLock.cvf";
                                         Line = 20L;
                                         Column = 18L;};
                                       Node = LV (LVIdent "t");});},
                                 View.Func {Name = "holdLock";
                                       Params = [];},
                                 View.Func
                                   {Name = "holdTick";
                                    Params =
                                     [{Position =
                                        {StreamName =
                                          "Examples/Pass/ticketLock.cvf";
                                         Line = 20L;
                                         Column = 50L;};
                                       Node = LV (LVIdent "t");}];}));}];},
                      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                                   Line = 21L;
                                   Column = 16L;};
                       Node =
                        BopExpr
                          (Neq,
                           {Position =
                             {StreamName = "Examples/Pass/ticketLock.cvf";
                              Line = 21L;
                              Column = 14L;};
                            Node = LV (LVIdent "s");},
                           {Position =
                             {StreamName = "Examples/Pass/ticketLock.cvf";
                              Line = 21L;
                              Column = 19L;};
                            Node = LV (LVIdent "t");});});};
                Post = Unmarked (View.Func {Name = "holdLock";
                                       Params = [];});}];};};

/// The correct parsing of the ticket lock's unlock method.
let ticketLockUnlockMethodAST =
    {Signature = {Name = "unlock";
                    Params = [];};
       Body =
        {Pre = Unmarked (View.Func {Name = "holdLock";
                               Params = [];});
         Contents =
          [{Command =
             {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                          Line = 30L;
                          Column = 5L;};
              Node =
               Command'.Prim
                 {PreAssigns = [];
                  Atomics =
                   [{Position =
                      {StreamName = "Examples/Pass/ticketLock.cvf";
                       Line = 30L;
                       Column = 6L;};
                     Node = Postfix (LVIdent "serving",Increment);}];
                  PostAssigns = [];};};
            Post = Unmarked Unit;}];};};

let ticketLockConstraint01 = 
  Definite
     (DView.Unit,
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 38L;
                   Column = 50L;};
       Node =
        BopExpr
          (Ge,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                           Line = 38L;
                           Column = 43L;};
               Node = LV (LVIdent "ticket");},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 38L;
                        Column = 53L;};
            Node = LV (LVIdent "serving");});})

let ticketLockConstraint02 =
  Definite
     (DView.Func {Name = "holdTick";
            Params = ["t"];},
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 41L;
                   Column = 50L;};
       Node =
        BopExpr
          (Gt,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                           Line = 41L;
                           Column = 43L;};
               Node = LV (LVIdent "ticket");},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 41L;
                        Column = 52L;};
            Node = LV (LVIdent "t");});})

let ticketLockConstraint03 =
  Definite
     (DView.Func {Name = "holdLock";
            Params = [];},
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 42L;
                   Column = 50L;};
       Node =
        BopExpr
          (Neq,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 42L;
                            Column = 43L;};
                Node = LV (LVIdent "ticket");},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 42L;
                        Column = 53L;};
            Node = LV (LVIdent "serving");});})

let ticketLockConstraint04 =
  Definite
     (DView.Join (DView.Func {Name = "holdLock";
                  Params = [];},DView.Func {Name = "holdTick";
                                      Params = ["t"];}),
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 45L;
                   Column = 51L;};
       Node =
        BopExpr
          (Neq,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 45L;
                            Column = 43L;};
                Node = LV (LVIdent "serving");},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 45L;
                        Column = 54L;};
            Node = LV (LVIdent "t");});})

let ticketLockConstraint05 =
  Definite
     (DView.Join (DView.Func {Name = "holdTick";
                  Params = ["ta"];}, DView.Func {Name = "holdTick";
                                          Params = ["tb"];}),
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 46L;
                   Column = 46L;};
       Node =
        BopExpr
          (Neq,{Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                            Line = 46L;
                            Column = 43L;};
                Node = LV (LVIdent "ta");},
           {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                        Line = 46L;
                        Column = 49L;};
            Node = LV (LVIdent "tb");});})

let ticketLockConstraint06 = 
  Definite
     (DView.Join (DView.Func {Name = "holdLock";
                  Params = [];},DView.Func {Name = "holdLock";
                                      Params = [];}),
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 47L;
                   Column = 43L;};
       Node = False;})

/// The parsed form of the ticket lock.
let ticketLockParsed =
      [ 
      { Position = { StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 34L;
                   Column = 1L; };
        Node = ViewProto {Name = "holdTick";
                         Params = [Int "t"];};};
      { Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 35L;
                   Column = 1L;};
        Node = ViewProto {Name = "holdLock";
                         Params = []} }

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
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
                   Line = 5L;
                   Column = 1L;};
       Node = Global (Int "ticket");};
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 6L;
                   Column = 1L;};
       Node = Global (Int "serving");};
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 7L;
                   Column = 1L;};
       Node = Local (Int "t");};
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 8L;
                   Column = 1L;};
       Node = Local (Int "s");}; 
        
      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 13L;
                   Column = 1L;};
       Node = Method ticketLockLockMethodAST;};

      {Position = {StreamName = "Examples/Pass/ticketLock.cvf";
                   Line = 28L;
                   Column = 1L;};
       Node = Method ticketLockUnlockMethodAST;};
       ]

/// The collated form of the ticket lock.
let ticketLockCollated =
    { CollatedScript.Globals =
          [ (TypedVar.Int "ticket")
            (TypedVar.Int "serving") ]
      Locals =
          [ (TypedVar.Int "t")
            (TypedVar.Int "s") ]
      Search = None
      VProtos =
          [ { Name = "holdTick"
              Params = [ (Int "t") ] }
            { Name = "holdLock"
              Params = [] } ]
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
                        command "!ILoad++" [ Int "t"; Int "ticket" ]
                             [ SMExpr.Int (siBefore "ticket") ]
                        |> List.singleton |> Prim
                    Post = Mandatory <| sing holdTick }
                  { Command =
                        While (isDo = true,
                               expr = BNot sIsT,
                               inner =
                                   { Pre = Mandatory <| sing holdTick
                                     Contents =
                                         [ { Command =
                                                 command "!ILoad" [ Int "s" ]
                                                      [ SMExpr.Int (siBefore "serving") ]
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
            // constraint holdTick(ta) * holdTick(tb) -> ta != tb;
            Contents =
                [ { Command =
                        command "!I++" [ Int "serving" ] [ SMExpr.Int (siBefore "serving") ]
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
                        command "!ILoad++"
                             [ Int "t"; Int "ticket" ]
                             [ SMExpr.Int (siBefore "t");
                               SMExpr.Int (siBefore "ticket"); ]
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
                                                      [ Int "s" ]
                                                      [ SMExpr.Int (siBefore "serving"); ]
                                                 |> List.singleton |> Prim
                                             Post =
                                                 Mandatory <|
                                                 Multiset.ofFlatList
                                                     [ gHoldLock sIsT
                                                       gHoldTick (BNot sIsT) ] } ] } )
                    Post = Mandatory <| sing (gHoldLock BTrue) } ] } }

/// The ticket lock's unlock method, in guarded form.
let ticketLockGuardedUnlock : GuarderMethod =
    { Signature = func "unlock" []
      Body =
          { Pre = Mandatory <| sing (gHoldLock BTrue)
            Contents =
                [ { Command =
                        command "!I++" [ Int "serving" ] [ Expr.Int (siBefore "serving") ]
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
                   Params = [ Int "t" ] } ] |> Multiset.toFlatList,
           BGt(siVar "ticket", siVar "t"))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] } ] |> Multiset.toFlatList,
           BNot (iEq (siVar "ticket") (siVar "serving")))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] }
                 { Name = "holdTick"
                   Params = [ Int "t" ] } ] |> Multiset.toFlatList,
           BNot(iEq (siVar "serving") (siVar "t")))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdTick"
                   Params = [ Int "ta" ] }
                 { Name = "holdTick"
                   Params = [ Int "tb" ] } ] |> Multiset.toFlatList,
           BNot(iEq (siVar "ta") (siVar "tb")))
      Definite
          (Multiset.ofFlatList
               [ { Name = "holdLock"
                   Params = [] }
                 { Name = "holdLock"
                   Params = [] } ] |> Multiset.toFlatList,
           BFalse) ]

/// The model of the ticket lock.
let ticketLockModel : Model<ModellerMethod, ViewToSymBoolDefiner> =
    { Globals =
          Map.ofList [ ("serving", Type.Int ())
                       ("ticket", Type.Int ()) ]
      Locals =
          Map.ofList [ ("s", Type.Int ())
                       ("t", Type.Int ()) ]
      Axioms = ticketLockMethods
      ViewDefs = ticketLockViewDefs
      Semantics = Starling.Lang.Modeller.coreSemantics }
