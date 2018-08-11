/// <summary>
///     Tests for collections.
/// </summary>
module Starling.Tests.Collections

open NUnit.Framework

open Starling.Tests.TestUtils

open Starling.Collections

module Multiset =
    module TestOfFlatList =
        let check flatList lst =
            let mset = Map.ofList lst |> MSet
            Multiset.ofFlatList flatList ?=? mset

        [<Test>]
        let ``Multiset.ofFlatList creates empty multiset`` () =
            check [] []

        [<Test>]
        let ``Multiset.ofFlatList multiple values`` () =
            check [1; 1] [ (1, 2) ]

        [<Test>]
        let ``Multiset.ofFlatList multiple keys`` () =
            check [1; 1; 2; 5; 2; 5; 7; 1]
                <| [ (1, 3)
                     (2, 2)
                     (5, 2)
                     (7, 1) ]

        module TestToFlatList =
            let check lst flatList =
                let mset = Map.ofList lst |> MSet
                Assert.AreEqual(flatList, Multiset.toFlatList mset)

            [<Test>]
            let ``Multiset.toFlatList empty`` () =
                check [] []

            [<Test>]
            let ``Multiset.toFlatList singleton`` () =
                check [ (1, 1) ]
                        [ 1 ]

            [<Test>]
            let ``Multiset.toFlatList multiple`` () =
                check [ (1, 2) ]
                        [ 1; 1 ]

            [<Test>]
            let ``Multiset.toFlatList repeated`` () =
                check [ (1, 2); ]
                        [ 1; 1; ]

            [<Test>]
            let ``Multiset.toFlatList big`` () =
                check [ (1, 2); (3, 1); (4, 5); ]
                        [ 1; 1; 3; 4; 4; 4; 4; 4; ]

    module TestMultisetAppend =
        let check inputMapList appendList outputMapList =
            let mset = MSet <| Map.ofList inputMapList
            let finalMSet = MSet <| Map.ofList outputMapList
            let appendMset = Multiset.ofFlatList appendList
            Multiset.append mset appendMset ?=? finalMSet

        [<Test>]
        let ``Multiset.append empty lhs`` () =
            check [] [1] [ (1, 1) ]

        [<Test>]
        let ``Multiset.append empty rhs`` () =
            check [ (1, 1) ] [] [ (1, 1) ]

        [<Test>]
        let ``Multiset.append increment`` () =
            check [ (1, 1) ] [1] [ (1, 2) ]

        [<Test>]
        let ``Multiset.append big`` () =
            check [ (1, 2); (2, 1); (3, 4) ] [1] [ (1, 3); (2, 1); (3, 4) ]

    module TestMultisetFold =
        let check inputFolderFunc inputMapList initial expectedOutput =
            let mset = MSet <| Map.ofList inputMapList
            let output = Multiset.fold inputFolderFunc initial mset
            output ?=? expectedOutput

        [<Test>]
        let ``Multiset.append empty lhs`` () =
            check (fun s _ _-> s) [] [] []
