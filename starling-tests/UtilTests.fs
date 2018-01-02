/// <summary>
///    Tests for <c>Starling.Utils</c> (not to be confused with <c>TestUtils</c>,
///    which contains helpers for testing).
/// </summary>
module Starling.Tests.Utils

open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.Utils

module TestFix =
    let inc = (+) 1
    let cnst x _ = x

    let check bound out =
        fix_bound := bound
        out ?=? (fix inc 0)

    [<Test>]
    let ``test fix bounding`` () =
        // check that (inc (inc (inc (0)))) = 3
        check 3 3

    [<Test>]
    let ``test fix fix-point`` () =
        // check that inc (inc (inc (0))) = 3
        3 ?=? fix (cnst 3) 0