/// <summary>
///     Utilities and types for working with expressions.
/// </summary>
module Starling.Tests.Core.Expr

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
                   (Int (AVar "foo"), 
                    Int (AVar "bar"));
                  BEq 
                   (Int (AVar "bar"), 
                    Int (AVar "foo"))
               ]), 
     BEq (Int (AVar "foo"), 
          Int (AVar "bar"))
   ) 

  [<Test>] 
  let ``Expression de-duplication, disjunction removal.`` () = 
    Assert.AreEqual (
     simp (BOr [ BEq 
                   (Int (AVar "foo"), 
                    Int (AVar "bar"));
                  BEq 
                   (Int (AVar "bar"), 
                    Int (AVar "foo"))
               ]), 
     BEq (Int (AVar "foo"), 
          Int (AVar "bar"))
   ) 

//])) , (BAnd [(Beq (AVar 0) (AVar 1))]) ) 
