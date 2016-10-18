/// <summary>
///     Part of the Starling tool that flattens terms, adding in globals.
/// </summary>
module Starling.Flattener

open Starling.Collections
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.Command
open Starling.Core.GuardedView


/// <summary>
///     Extracts a sequence of all of the parameters in a func sequence
/// </summary>
let paramsOfFuncSeq (funcs : Func<'var> seq) : 'var seq =
    funcs |> Seq.map (fun v -> v.Params) |> Seq.concat

/// <summary>
///     Constructs a (hopefully) unique name for a Func resulting from
///     the flattening of a func sequence
/// </summary>
let genFlatFuncSeqName (funcs : Func<'var> seq) : string =
    funcs
    // These two steps are to ensure we don't capture an existing name.
    |> Seq.map (fun { Name = n } -> n.Replace("_", "__"))
    |> scons "v"
    |> String.concat "_"
    // This step ensures that the empty view is named 'emp', not 'v'.
    |> fun s -> if s = "v" then "emp" else s

let genFlatIteratedFuncName ifcs =
    let funcs = Seq.map (fun ifc -> ifc.Func) ifcs
    genFlatFuncSeqName funcs

let paramsFromIteratedFunc funcContainer =
    let funcParams = Seq.ofList funcContainer.Func.Params
    maybe funcParams (flip scons funcParams) funcContainer.Iterator

/// <summary>
///     Constructs a Func from a DView
/// </summary>
/// <param name="svars">
///     The set of shared variables in use, to be merged into the func.
/// </param>
/// <param name="dview">
///     The DView to use in construction.
/// </param>
/// <returns>
///     A new Func containing all parameters of the individuals as well as their iterators
///     with the shared variables appended
/// </returns>
let flattenDView (svars : TypedVar seq) (dview : DView) : DFunc =
    // TODO: What if iterators share names? e.g. iterated A [n] * iterated B [n]
    let ownParams = Seq.concat (Seq.map paramsFromIteratedFunc dview)
    let allParams = Seq.append svars ownParams
    { Name = genFlatIteratedFuncName dview; Params = Seq.toList allParams }

/// Flattens an OView into an SMVFunc given the set of globals
let flattenOView (svarExprs : Expr<Sym<MarkedVar>> seq) (oview : OView)
  : SMVFunc =
    { Name = genFlatFuncSeqName oview
      Params = Seq.toList (Seq.append svarExprs (paramsOfFuncSeq oview)) }

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
            (Seq.map (mapItem (flattenOView (globalsF Before)))
             >> Multiset.ofFlatSeq)
            (flattenOView (globalsF After))

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
    let globalsF marker = varMapToExprs (marker >> Reg) model.SharedVars

    /// Build a list of global parameters, for view definitions.
    let globalsP = toVarSeq model.SharedVars

    { SharedVars = model.SharedVars
      ThreadVars = model.ThreadVars
      Axioms = Map.map (fun _ x -> flattenTerm globalsF x) model.Axioms
      ViewDefs =
          model.ViewDefs
          |> ViewDefiner.toSeq
          |> Seq.map (pairMap (flattenDView globalsP) id)
          |> FuncDefiner.ofSeq
      Semantics = model.Semantics
      ViewProtos = model.ViewProtos
      DeferredChecks = model.DeferredChecks }
