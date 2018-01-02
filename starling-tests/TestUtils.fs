/// <summary>
///    Utilities for testing (not to be confused with <c>UtilTests</c>,
///    which tests utilities.
/// </summary>
module Starling.Tests.TestUtils

open Chessie.ErrorHandling

open NUnit.Framework

let assertEqual<'a when 'a: equality> (a : 'a) (b : 'a) = Assert.AreEqual(a, b)
let AssertAreEqual(a, b) = assertEqual a b

/// <summary>
///     Asserts that a Chessie result failed with a given result list.
/// </summary>
let assertFail
    (expected: 'Error list)
    (actualResult : Result<'Val, 'Error>)
    (pVal : 'Val -> string)
    : unit =
    match actualResult with
    | Fail actuals ->
        assertEqual (List.sort expected) (List.sort actuals)
    | Warn (v, _) | Pass v ->
        let fmsg = sprintf "Got successful result:\n%s" (pVal v)
        Assert.Fail(fmsg)


let assertOkAndEqual
    (expected: 'Val)
    (actualResult : Result<'Val, 'Error>)
    (pError : 'Error -> string)
    : unit =
    match actualResult with
    | Pass actual -> assertEqual expected actual
    | Warn (_, warns) | Fail warns ->
        let warnstr = String.concat "\n" (List.map pError warns)
        let fmsg = sprintf "Got errors:\n%s" warnstr
        Assert.Fail(fmsg)

let inline (?=?) a b = assertEqual a b

/// <summary>
///     A more F#-friendly overload of <c>TestCaseData</c>.
/// </summary>
let tcd : obj[] -> TestCaseData = TestCaseData