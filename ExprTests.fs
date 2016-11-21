/// <summary>
///     Utilities and types for working with expressions.
/// </summary>
module Starling.Tests.Core.Expr

open Starling.Utils
open Starling.Core.TypeSystem
open NUnit.Framework

open Starling.Core.Expr 

module ExprSimp =

  [<Test>] 
  let ``Expression simplification on trivial conjunctions.`` () = 
    Assert.AreEqual (
      (simp (BAnd [BTrue; BTrue])), 
      BTrue
    )

  [<Test>] 
  let ``Expression de-duplication, conjuction removal.`` () = 
    Assert.AreEqual (
     simp (BAnd [ BEq 
                   (Int (IVar "foo"), 
                    Int (IVar "bar"));
                  BEq 
                   (Int (IVar "bar"), 
                    Int (IVar "foo"))
               ]), 
     BEq (Int (IVar "foo"), 
          Int (IVar "bar"))
   ) 

  [<Test>] 
  let ``Expression de-duplication, disjunction removal.`` () = 
    Assert.AreEqual (
     simp (BOr [ BEq 
                   (Int (IVar "foo"), 
                    Int (IVar "bar"));
                  BEq 
                   (Int (IVar "bar"), 
                    Int (IVar "foo"))
               ]), 
     BEq (Int (IVar "foo"), 
          Int (IVar "bar"))
   ) 
