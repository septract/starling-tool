/// <summary>
///    Tests for <c>Starling.Core.Semantics</c>.
/// </summary>
module Starling.Tests.Semantics

open NUnit.Framework
open Starling
open Starling.Collections
open Starling.Utils
open Starling.Utils.Testing
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Expr
open Starling.Core.Symbolic
open Starling.Core.Var
open Starling.Core.Model
open Starling.Semantics
open Starling.Tests.Studies

/// Tests for the semantic transformer.
type SemanticsTests() =
    /// Test cases for composition.
    static member Compositions =
        [ (tcd
               [| bEq (sbAfter "foo") (sbBefore "bar")
                  bEq (sbAfter "baz") (sbBefore "foo") |])
              .Returns(BAnd [ bEq (sbInter 0I "foo") (sbBefore "bar")
                              bEq (sbAfter "baz") (sbInter 0I "foo") ] )
              .SetName("Compose two basic assignments")
          (tcd
               [| BAnd
                      [ bEq (sbInter 0I "foo") (sbBefore "bar")
                        bEq (sbAfter "baz") (sbInter 0I "foo") ]
                  BAnd
                      [ bEq (sbInter 0I "flop") (sbBefore "baz")
                        bEq (sbAfter "froz") (sbInter 0I "flop") ] |] )
              // TODO(CaptainHayashi): make this not order-dependent... somehow
              .Returns(BAnd
                           [ bEq (sbInter 1I "baz") (sbInter 0I "foo")
                             bEq (sbInter 0I "foo") (sbBefore "bar")
                             bEq (sbAfter "froz") (sbInter 2I "flop")
                             bEq (sbInter 2I "flop") (sbInter 1I "baz") ] )
              .SetName("Compose two compositions") ]

    /// Tests whether composition behaves itself.
    [<TestCaseSource("Compositions")>]
    member this.``Boolean composition should work correctly`` x y =
        composeBools x y

    /// <summary>
    ///     Test cases for the variable framer.
    /// </summary>
    static member FrameVars =
        [ TestCaseData(VarDecl.Int "foo")
              .Returns(iEq (siAfter "foo") (siBefore "foo"))
              .SetName("Frame an integer variable")
          TestCaseData(VarDecl.Bool "bar")
              .Returns(bEq (sbAfter "bar") (sbBefore "bar"))
              .SetName("Frame a Boolean variable") ]

    /// <summary>
    ///     Tests <c>frameVar</c>.
    /// </summary>
    [<TestCaseSource("FrameVars")>]
    member x.``Test framing of individual variables`` var =
        frameVar var

    // Test cases for the expression framer.
    static member FrameExprs =
        [ TestCaseData(BTrue : SMBoolExpr)
              .Returns( [ iEq (siAfter "serving") (siBefore "serving")
                          iEq (siAfter "ticket") (siBefore "ticket")
                          iEq (siAfter "s") (siBefore "s")
                          iEq (siAfter "t") (siBefore "t") ] )
              .SetName("Frame id using the ticket lock model")

          TestCaseData(BAnd
                           [ BGt(siAfter "ticket", siBefore "ticket")
                             BLe(siAfter "serving", siBefore "serving")
                             iEq (siBefore "s") (siBefore "t") ] )
              .Returns( [ iEq (siAfter "s") (siBefore "s")
                          iEq (siAfter "t") (siBefore "t") ] )
              .SetName("Frame a simple command expression using the ticket lock model") ]

    // Test framing of expressions.
    [<TestCaseSource("FrameExprs")>]
    member x.``Test framing of expressions using the ticket lock model`` expr =
        frame
            (ticketLockModel.Globals)
            (ticketLockModel.Locals)
            expr

    /// Test cases for full command semantic translation.
    static member Commands =
        [ TestCaseData([ command "Assume" [] [ Expr.Bool <| iEq (siBefore "s") (siBefore "t") ]] )
              .Returns(Some <| Set.ofList
                           [ iEq (siAfter "serving") (siBefore "serving")
                             iEq (siAfter "ticket") (siBefore "ticket")
                             iEq (siAfter "s") (siBefore "s")
                             iEq (siAfter "t") (siBefore "t")
                             iEq (siBefore "s") (siBefore "t") ])
              .SetName("Semantically translate <assume(s == t)> using the ticket lock model")
          TestCaseData([ command "!I++" [ Param.Int "serving" ] [ Expr.Int <| siBefore "serving" ] ] )
              .Returns(Some <| Set.ofList
                           [ iEq (siAfter "ticket") (siBefore "ticket")
                             iEq (siAfter "s") (siBefore "s")
                             iEq (siAfter "t") (siBefore "t")
                             iEq (siAfter "serving") (AAdd [ siBefore "serving"; AInt 1L ]) ])
              .SetName("Semantically translate <serving++> using the ticket lock model") ]

    // Test semantic reification of commands.
    [<TestCaseSource("Commands")>]
    member x.``Test semantic translation of commands using the ticket lock model`` com =
        com
        |> semanticsOfCommand
               (Starling.Lang.Modeller.coreSemantics)
               (ticketLockModel.Globals)
               (ticketLockModel.Locals)
        |> okOption
        |> Option.bind (function
                        | BAnd xs -> xs |> Set.ofList |> Some
                        | _ -> None)
