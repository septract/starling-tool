/// <summary>
///     Part of the Starling tool that flattens terms, adding in globals.
/// </summary>
module Starling.Flattener

open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Var
open Starling.Core.GuardedView


/// <summary>
///     Extracts a sequence of all of the parameters in an func sequence
///     (OView or DView) in order.
/// </summary>
let paramsOfFuncSeq (funcs : Func<'var> seq) : 'var seq =
    funcs |> Seq.map (fun v -> v.Params) |> Seq.concat

/// <summary>
///     Constructs a (hopefully) unique name for a Func resulting from
///     the flattening of a func sequence (OView or DView).
/// </summary>
let genFlatFuncSeqName (funcs : Func<'var> seq) : string =
    funcs
    // These two steps are to ensure we don't capture an existing name.
    |> Seq.map (fun { Name = n } -> n.Replace("_", "__"))
    |> scons "v"
    |> String.concat "_"
    // This step ensures that the empty view is named 'emp', not 'v'.
    |> fun s -> if s = "v" then "emp" else s

/// <summary>
///     Constructs a Func from a func sequence, appending global variables.
/// </summary>
/// <param name="globals">
///     The set of active globals, in expression form, which will be appended
///     into the Func's parameter list.
/// </param>
/// <param name="funcs">
///     The Func sequence to flatten.
/// </param>
/// <returns>
///     A new SMVFunc containing all of the parameters of the constituent
///     funcs, as well as the globals list, and a new unique name.
/// </returns>
let flattenFuncSeq
  (globals : 'var seq)
  (oview : Func<'var> seq)
  : Func<'var> =
    { Name = genFlatFuncSeqName oview
      Params = oview |> paramsOfFuncSeq |> Seq.append globals |> List.ofSeq }

/// <summary>
///     Flattens a term by converting all of its OViews into single funcs.
/// </summary>
/// <param name="globalsF">
///     A function that takes a marker (Before, After, etc.) and returns
///     a sequence of all global variables converted into symbolic marked
///     expressions with said marker.
/// </param>
/// <returns>
///     A function mapping terms over OViews to terms over SMVFuncs.
/// </returns>
let flattenTerm
  (globalsF : (Var -> MarkedVar) -> SMExpr seq)
  : Term<_, Set<GuardedSubview>, OView>
  -> Term<_, GView<Sym<MarkedVar>>, SMVFunc> =
    mapTerm id
            (Seq.map (mapItem (flattenFuncSeq (globalsF Before)))
             >> Multiset.ofFlatSeq)
            (flattenFuncSeq (globalsF After))

/// <summary>
///    Flattens all func sequences in a model, turning them into funcs.
///    <para>
///        This allows each combination of views coming out of reification
///        to be represented by a single uninterpreted function, which can
///        then either be interpreted using the corresponding ViewDefs,
///        or inferred by using a solver like HSF.
///    </para>
/// </summary>
/// <param name="model">
///     The model to flatten.
/// </param>
/// <returns>
///     The flattened model.
/// </returns>
let flatten
  (model : Model<Term<_, Set<GuardedSubview>, OView>,
                 ViewDefiner<SVBoolExpr option>>)
  : Model<Term<_, GView<Sym<MarkedVar>>, SMVFunc>,
          FuncDefiner<SVBoolExpr option>> =
    /// Build a function making a list of global arguments, for view assertions.
    let globalsF marker = varMapToExprs (marker >> Reg) model.Globals

    /// Build a list of global parameters, for view definitions.
    let globalsP =
        model.Globals
        |> Map.toSeq
        |> Seq.map (fun (name, ty) -> withType ty name)
        |> List.ofSeq

    { Globals = model.Globals
      Locals = model.Locals
      Axioms = Map.map (fun _ x -> flattenTerm globalsF x) model.Axioms
      ViewDefs =
          model.ViewDefs
          |> ViewDefiner.toSeq
          |> Seq.map (pairMap (flattenFuncSeq globalsP) id)
          |> FuncDefiner.ofSeq
      Semantics = model.Semantics }


/// <summary>
///     Tests for <c>Flattener</c>.
/// </summary>
module Tests =
    open NUnit.Framework
    open Chessie.ErrorHandling
    open Starling.Utils.Testing


    /// <summary>
    ///     NUnit tests for <c>Flattener</c>.
    /// </summary>
    type NUnit () =
        /// The globals environment used in the tests.
        static member Globals : VarMap =
            returnOrFail <| makeVarMap
                [ TypedVar.Int "serving"
                  TypedVar.Int "ticket" ]

        /// Test cases for the view func renamer.
        static member ViewFuncNamings =
            let ms : SMVFunc list -> OView = Multiset.ofFlatList >> Multiset.toFlatList
            [ TestCaseData(ms [ { Name = "foo"; Params = [] }
                                { Name = "bar_baz"; Params = [] } ])
                .Returns("v_bar__baz_foo") // Remember, multisets sort!
                .SetName("Encode func name of view 'foo() * bar_baz()' as 'v_bar__baz_foo'")
              TestCaseData(ms []).Returns("emp")
                .SetName("Encode func name of view '' as 'emp'") ]

        /// Tests the view predicate name generator.
        [<TestCaseSource("ViewFuncNamings")>]
        member x.``the flattened view name generator generates names correctly`` v =
            (genFlatFuncSeqName : OView -> string) v

        /// Test cases for the full defining-view func converter.
        /// These all use the Globals environment above.
        static member DViewFuncs =
            let ms : DFunc list -> DView = Multiset.ofFlatList >> Multiset.toFlatList
            [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                                { Name = "holdTick"; Params = [ Int "t" ] } ])
                 .Returns({ Name = "v_holdLock_holdTick"
                            Params =
                                [ Int "serving"
                                  Int "ticket"
                                  Int "t" ] } : DFunc)
                .SetName("Convert defining view 'holdLock() * holdTick(t)' to defining func") ]

        /// Tests the viewdef LHS translator.
        [<TestCaseSource("DViewFuncs")>]
        member x.``the defining view func translator works correctly`` (v : DView) =
            v
            |> flattenFuncSeq
                   (NUnit.Globals
                    |> Map.toSeq
                    |> Seq.map (fun (n, t) -> withType t n))

        /// Test cases for the full view func converter.
        /// These all use the Globals environment above.
        static member ViewFuncs =
            let ms : SMVFunc list -> OView = Multiset.ofFlatList >> Multiset.toFlatList
            [ TestCaseData(ms [ { Name = "holdLock"; Params = [] }
                                { Name = "holdTick"; Params = [ Expr.Int (siBefore "t") ] } ])
                 .Returns({ Name = "v_holdLock_holdTick"
                            Params =
                                [ Expr.Int (siBefore "serving")
                                  Expr.Int (siBefore "ticket")
                                  Expr.Int (siBefore "t") ] })
                .SetName("Convert 'holdLock() * holdTick(t)' to func") ]

        /// Tests the viewdef LHS translator.
        [<TestCaseSource("ViewFuncs")>]
        member x.``the view func translator works correctly`` (v : OView) =
            v
            |> flattenFuncSeq
                   (NUnit.Globals
                    |> Map.toSeq
                    |> Seq.map
                           (function
                            | (x, Type.Int ()) -> x |> siBefore |> Expr.Int
                            | (x, Type.Bool ()) -> x |> sbBefore |> Expr.Bool))
