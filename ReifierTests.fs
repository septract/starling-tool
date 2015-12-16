/// Tests for the reifier.
module Starling.Tests.Reifier

open Starling.Collections
open Starling.Var
open Starling.Model
open Starling.Reifier
open Starling.Z3.Reifier
open Starling.Tests.Studies

open Microsoft
open Fuchu

let testFindDefOfView ctx =
    testList
        "Test findDefOfView"
        [testCase "Test findDefOfView on reversed ticketed lock views" <|
         // TODO(CaptainHayashi): this test is practically useless because of
         // the List.sort.
             fun _ ->
                 let model = ticketLockModel ctx
                 Assert.Equal
                    ("viewdef of [holdTick(t) * holdLock()] <> [holdLock() * holdTick(t)]",
                     Some {CViews = Multiset.ofList
                                        [ {VName = "holdLock"
                                           VParams = [] }
                                          {VName = "holdTick"
                                           VParams = [(Int, "t")] } ]
                           CZ3 = ctx.MkNot (ctx.MkEq (ctx.MkIntConst "serving",
                                                      ctx.MkIntConst "t")) },
                     findDefOfView model
                                   (Multiset.ofList
                                        [ {VName = "holdTick"
                                           VParams = [ctx.MkIntConst "t"] }
                                          {VName = "holdLock"
                                           VParams = [] } ] )) ]

/// Tests various properties of the reifier.
[<Tests>]
let testReifier =
    let ctx = new Z3.Context ()
    let t =
        testList
            "Test the reifier"
            [ testFindDefOfView ctx ]
    ctx.Dispose ()
    t
