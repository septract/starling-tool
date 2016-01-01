/// Tests for the reifier.
module Starling.Tests.Reifier

open NUnit.Framework
open Starling.Collections
open Starling.Var
open Starling.Model
open Starling.Reifier
open Starling.Z3.Translator
open Starling.Tests.Studies
open Microsoft

/// Tests for the reifier.
type ReifierTests() = 
    
    /// Test cases for findDefOfView.
    static member FindDefOfViewCases = 
        seq {
            // Correct order 
            yield (new TestCaseData(fun (ctx : Z3.Context) -> 
            (Multiset.ofList [ { Name = "holdLock"
                                 Params = [] }
                               { Name = "holdTick"
                                 Params = [ ctx.MkIntConst "t" :> Z3.Expr ] } ]))).Returns(Some(Multiset.ofList [ { Name = "holdLock"
                                                                                                                    Params = [] }
                                                                                                                  { Name = "holdTick"
                                                                                                                    Params = [ (Type.Int, "t") ] } ]))
            // Reversed order
            yield (new TestCaseData(fun (ctx : Z3.Context) -> 
            (Multiset.ofList [ { Name = "holdTick"
                                 Params = [ ctx.MkIntConst "t" :> Z3.Expr ] }
                               { Name = "holdLock"
                                 Params = [] } ]))).Returns(Some(Multiset.ofList [ { Name = "holdLock"
                                                                                     Params = [] }
                                                                                   { Name = "holdTick"
                                                                                     Params = [ (Type.Int, "t") ] } ]))
        }
    
    [<TestCaseSource("FindDefOfViewCases")>]
    /// Tests whether findDefOfView behaves correctly.
    member x.``findDefOfView finds view defs correctly on the ticketed lock`` (vdf : Z3.Context -> Multiset<View>) = 
        use ctx = new Z3.Context()
        let view = vdf ctx
        view
        |> findDefOfView (ticketLockModel ctx)
        |> Option.map (fun x -> x.CViews)
