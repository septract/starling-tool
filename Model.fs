/// <summary>
///   Module of model types and functions.
/// </summary>
module Starling.Core.Model

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.Expr
open Starling.Core.Var


(*
 * Starling uses the following general terminology for model items.
 * (Note that these terms differ from their CamelCasedAndPrefixed
 * counterparts, whose meanings are given in their documentation comments.)
 *
 * func: a single term, usually Name(p1, p2, .., pn), in a view.
 *
 * view: an entire view expression, or multiset, of funcs.
 *
 * guarded: Starling represents case splits in its proof theory by
 *          surrounding a view or func whose presence in the proof is
 *          conditional with an expression true if or only if it is
 *          present; such a view or func is 'guarded'.
 *
 * view-set: a multiset of guarded views.
 *
 * conds: a pair of view assertions.
 *
 * axiom: a Hoare triple, containing a pair of conds, and some
 *        representation of a command.
 *
 * prim: a structured representation of an axiom command.
 *)


/// <summary>
///     Model types.
/// </summary
[<AutoOpen>]
module Types =
    (*
     * Guards
     *)

    /// A guarded item.
    /// The semantics of a Guarded Item is that the Item is to be taken as
    /// present in its parent context (eg a View) if, and only if, Cond holds.
    type Guarded<'a> =
        { Cond : BoolExpr
          Item : 'a }

    (*
     * Funcs (other than Starling.Collections.Func)
     *)

    /// A func over expressions, used in view expressions.
    type VFunc = Func<Expr>

    /// A view-definition func.
    type DFunc = Func<Type * string>

    /// A guarded view func.
    type GFunc = Guarded<VFunc>

    (*
     * Views
     *)

    /// <summary>
    ///     A basic view, as a multiset of VFuncs.
    /// </summary>
    /// <remarks>
    ///     Though View is the canonical Concurrent Views Framework view,
    ///     we actually seldom use it.
    /// </remarks>
    type View = Multiset<VFunc>

    /// A view definition.
    type DView = Multiset<DFunc>

    /// <summary>
    ///     A guarded view.
    /// </summary>
    /// <remarks>
    ///     These are the most common form of view in Starling internally,
    ///     although theoretically speaking they are equivalent to Views
    ///     with the guards lifting to proof case splits.
    /// </remarks>
    type GView = Multiset<GFunc>

    /// <summary>
    ///     A command.
    /// </summary>
    /// <remarks>
    ///     <para>
    ///         Commands are keys into the <c>Semantics</c> <c>FuncTable</c>
    ///         in the model.  This table contains two-state Boolean
    ///         expressions capturing the command's semantics in a
    ///         sort-of-denotational way.
    ///     </para>
    ///     <para>
    ///         Commands are implemented in terms of <c>VFunc</c>s for
    ///         convenience, not because of any deep relationship between
    ///         the two concepts.
    ///     </para>
    /// </remarks>
    type Command = VFunc

    (*
     * View sets
     *)

    /// A set of guarded views, as produced by reification.
    type ViewSet = Multiset<Guarded<View>>

    (*
     * View definitions
     *)

    /// <summary>
    ///     A view definition.
    /// </summary>
    /// <remarks>
    ///     The semantics of a ViewDef is that, if Def is present, then the
    ///     view View is satisfied if, and only if, Def holds.
    /// </remarks>
    type ViewDef<'view> =
        { View : 'view
          Def : BoolExpr option }

    (*
     * Terms
     *)

    /// <summary>
    ///     A term, containing a command relation, weakest precondition, and
    ///     goal.
    /// </summary>
    /// <remarks>
    ///     Though these are similar to Axioms, we keep them separate for
    ///     reasons of semantics: Axioms are literal Hoare triples {P}C{Q},
    ///     whereas Terms are some form of the actual Views axiom soundness
    ///     check we intend to prove.
    /// </remarks>
    type Term<'cmd, 'wpre, 'goal> =
        { /// The command relation of the Term.
          Cmd : 'cmd
          /// The weakest precondition of the Term.
          WPre : 'wpre
          /// The intended goal of the Term, ie the frame to preserve.
          Goal : 'goal
        }

    /// A term over <c>Command</c>s.
    type PTerm<'wpre, 'goal> = Term<Command, 'wpre, 'goal>

    /// A term over semantic-relation commands.
    type STerm<'wpre, 'goal> = Term<BoolExpr, 'wpre, 'goal>

    /// <summary>
    ///     A 'Datalog-style' term of one goal <c>VFunc</c> and a
    ///     weakest-precondition <c>GView</c>.
    /// </summary>
    type DTerm = STerm<GView, VFunc>

    /// A term using only internal boolean expressions.
    type FTerm = STerm<BoolExpr, BoolExpr>

    (*
     * Models
     *)

    /// A parameterised model of a Starling program.
    type Model<'axiom, 'dview> =
        { Globals : VarMap
          Locals : VarMap
          Axioms : Map<string, 'axiom>
          /// <summary>
          ///     The semantic function for this model.
          /// </summary>
          Semantics : (DFunc * BoolExpr) list
          // This corresponds to the function D.
          ViewDefs : ViewDef<'dview> list }


/// <summary>
///     Pretty printers for the model.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Expr.Pretty

    /// Pretty-prints a type-name parameter.
    let printParam (ty, name) =
        hsep [ ty |> printType
               name |> String ]

    /// Pretty-prints a multiset given a printer for its contents.
    let printMultiset pItem =
        Multiset.toList
        >> List.map pItem
        >> semiSep

    /// Pretty-prints a guarded item.
    let printGuarded pitem {Cond = c; Item = i} =
        // Don't bother showing the guard if it's always true.
        if isTrue c then pitem i
        else
            parened (HSep([ printBoolExpr c
                            pitem i ], String "|"))

    /// Pretty-prints a VFunc.
    let printVFunc = printFunc printExpr

    /// Pretty-prints a guarded view.
    let printGFunc = printGuarded printVFunc

    /// Pretty-prints a DFunc.
    let printDFunc = printFunc printParam

    /// Pretty-prints a View.
    let printView = printMultiset printVFunc

    /// Pretty-prints a DView.
    let printDView = printMultiset printDFunc >> squared

    /// Pretty-prints a GView.
    let printGView = printMultiset printGFunc >> ssurround "<|" "|>"

    /// Pretty-prints a Command.
    let printCommand = printVFunc

    /// Pretty-prints a view set.
    let printViewSet =
        printMultiset (printGuarded printView >> ssurround "((" "))")
        >> ssurround "(|" "|)"

    /// Pretty-prints a term, given printers for its commands and views.
    let printTerm pCmd pWPre pGoal {Cmd = c; WPre = w; Goal = g} = 
        vsep [ headed "Command" (c |> pCmd |> Seq.singleton)
               headed "W/Prec" (w |> pWPre |> Seq.singleton)
               headed "Goal" (g |> pGoal |> Seq.singleton) ]

    /// Pretty-prints a PTerm.
    let printPTerm pWPre pGoal = printTerm printCommand pWPre pGoal

    /// Pretty-prints an STerm.
    let printSTerm pWPre pGoal = printTerm printBoolExpr pWPre pGoal

    /// Pretty-prints model variables.
    let printModelVar (name, ty) =
        colonSep [ String name
                   printType ty ]

    /// Pretty-prints a model constraint.
    let printViewDef pView { View = vs; Def = e } =
        printAssoc Inline
            [ (String "View", pView vs)
              (String "Def", withDefault (String "?")
                                         (Option.map printBoolExpr e)) ]

    /// Pretty-prints the axiom map for a model.
    let printModelAxioms pAxiom model =
        printMap Indented String pAxiom model.Axioms

    /// Pretty-prints a model given axiom and defining-view printers.
    let printModel pAxiom pDView model =
        headed "Model"
            [ headed "Shared variables" <|
                  Seq.singleton
                      (printMap Inline String printType model.Globals)
              headed "Thread variables" <|
                  Seq.singleton
                      (printMap Inline String printType model.Locals)
              headed "ViewDefs" <|
                  List.map (printViewDef pDView) model.ViewDefs
              headed "Axioms" <|
                  Seq.singleton (printModelAxioms pAxiom model) ]

    /// <summary>
    ///     Enumerations of ways to view part or all of a <c>Model</c>.
    /// </summary>
    type ModelView =
        /// <summary>
        ///     View the entire model.
        /// </summary>
        | Model
        /// <summary>
        ///     View the model's terms.
        /// </summary>
        | Terms
        /// <summary>
        ///     View a specific term.
        /// </summary>
        | Term of string

    /// <summary>
    ///     Prints a model using the <c>ModelView</c> given.
    /// </summary>
    /// <param name="mview">
    ///     The <c>ModelView</c> stating which part of the model should be
    ///     printed.
    /// </param>
    /// <param name="pAxiom">
    ///     The printer to use for model axioms.
    /// </param>
    /// <param name="pViewDef">
    ///     The printer to use for view definitions.
    /// </param>
    /// <param name="model">
    ///     The model to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command printing the part of
    ///     <paramref name="model" /> specified by
    ///     <paramref name="mView" />.
    /// </returns>
    let printModelView mView pAxiom pViewDef m =
        match mView with
        | ModelView.Model -> printModel pAxiom pViewDef m
        | ModelView.Terms -> printModelAxioms pAxiom m
        | ModelView.Term termstr ->
            Map.tryFind termstr m.Axioms
            |> Option.map pAxiom
            |> withDefault (termstr |> sprintf "no term '%s'" |> String)


/// <summary>
///     Type-constrained version of <c>func</c> for <c>DFunc</c>s.
/// </summary>
/// <parameter name="name">
///     The name of the <c>DFunc</c>.
/// </parameter>
/// <parameter name="pars">
///     The parameters of the <c>DFunc</c>, as a sequence.
/// </parameter>
/// <returns>
///     A new <c>DFunc</c> with the given name and parameters.
/// </returns>
let dfunc name (pars : (Type * string) seq) : DFunc = func name pars

/// <summary>
///     Type-constrained version of <c>func</c> for <c>VFunc</c>s.
/// </summary>
/// <parameter name="name">
///     The name of the <c>VFunc</c>.
/// </parameter>
/// <parameter name="pars">
///     The parameters of the <c>VFunc</c>, as a sequence.
/// </parameter>
/// <returns>
///     A new <c>VFunc</c> with the given name and parameters.
/// </returns>
let vfunc name (pars : Expr seq) : VFunc = func name pars

/// <summary>
///     Creates a new <c>GFunc</c>.
/// </summary>
/// <param name="guard">
///     The guard on which the <c>GFunc</c> is conditional.
/// </param>
/// <param name="name">
///     The name of the <c>GFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>GFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>GFunc</c> with the given guard, name, and parameters.
/// </returns>
let gfunc guard name pars = { Cond = guard ; Item = func name pars }

/// Rewrites a Term by transforming its Cmd with fC, its WPre with fW,
/// and its Goal with fG.
let mapTerm fC fW fG {Cmd = c; WPre = w; Goal = g} =
    {Cmd = fC c; WPre = fW w; Goal = fG g}

/// Rewrites a Term by transforming its Cmd with fC, its WPre with fW,
/// and its Goal with fG.
/// fC, fW and fG must return Chessie results; liftMapTerm follows suit.
let tryMapTerm fC fW fG {Cmd = c; WPre = w; Goal = g} =
    trial {
        let! cR = fC c;
        let! wR = fW w;
        let! gR = fG g;
        return {Cmd = cR; WPre = wR; Goal = gR}
    }

/// Returns the axioms of a model.
let axioms {Axioms = xs} = xs

/// Creates a new model that is the input model with a different axiom set.
/// The axiom set may be of a different type.
let withAxioms (xs : Map<string, 'y>) (model : Model<'x, 'dview>)
    : Model<'y, 'dview> =
    { Globals = model.Globals
      Locals = model.Locals
      ViewDefs = model.ViewDefs
      Semantics = model.Semantics
      Axioms = xs }

/// Maps a pure function f over the axioms of a model.
let mapAxioms (f : 'x -> 'y) (model : Model<'x, 'dview>) : Model<'y, 'dview> =
    withAxioms (model |> axioms |> Map.map (fun _ -> f)) model

/// Maps a failing function f over the axioms of a model.
let tryMapAxioms (f : 'x -> Result<'y, 'e>) (model : Model<'x, 'dview>)
    : Result<Model<'y, 'dview>, 'e> =
    lift (fun x -> withAxioms x model)
         (model
          |> axioms
          |> Map.toSeq
          |> Seq.map (fun (k, v) -> v |> f |> lift (mkPair k))
          |> collect
          |> lift Map.ofList)
