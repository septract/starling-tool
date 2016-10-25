/// <summary>
///   Module of model types and functions.
/// </summary>
module Starling.Core.Model

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Definer
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.View
open Starling.Core.Command


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
 *
 * We also use the following prefixes in type synonyms:
 *
 * M: markedvar
 * G: guarded
 * S: sym
 *)


/// <summary>
///     Model types.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     Mid-level register transfer logic used to encode Starling
    ///     commands.
    /// </summary>
    /// <typeparam name="L">The type of lvalues.</typeparam>
    type Microcode<'L> =
        /// <summary>An assignment.</summary>
        | Assign of lvalue : 'L * rvalue : Expr<Sym<Var>>
        /// <summary>A diverging assertion.</summary>
        | Assume of assumption : BoolExpr<Sym<Var>>
        /// <summary>A conditional.</summary>
        | Branch of conditional : BoolExpr<Sym<Var>>
                  * ifTrue : Microcode<'L> list
                  * ifFalse : Microcode<'L> list

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
          Goal : 'goal }
        override this.ToString() = sprintf "%A" this

    /// <summary>
    ///     A term over <c>Command</c>s.
    /// </summary>
    /// <typeparam name="wpre">
    ///     The type of the weakest-precondition part of the term.
    /// </typeparam>
    /// <typeparam name="goal">
    ///     The type of the goal part of the term.
    /// </typeparam>
    type PTerm<'wpre, 'goal> = Term<Command, 'wpre, 'goal>


    /// A term over semantic-relation commands.
    type STerm<'wpre, 'goal> = Term<SMBoolExpr, 'wpre, 'goal>

    /// A term using the same representation for all parts.
    type CTerm<'repr> = Term<'repr, 'repr, 'repr>

    type CmdTerm<'Semantics, 'WPre, 'Goal> = Term<CommandSemantics<'Semantics>, 'WPre, 'Goal>

    /// A term using only internal boolean expressions.
    type FTerm = CTerm<MBoolExpr>

    type PrimSemantics = { Name: string; Results: TypedVar list; Args: TypedVar list; Body: Microcode<TypedVar> list }
    type SemanticsMap<'a> = Map<string, 'a>
    type PrimSemanticsMap = SemanticsMap<PrimSemantics>

    /// <summary>
    ///     Information about a view prototype.
    /// </summary>
    type ProtoInfo =
        { /// <summary>
          ///     Whether the prototyped func is iterated, and thus needs
          ///     to be lowered and mentioned only in downclosed iterated
          ///     constraints.
          /// </summary>
          IsIterated : bool
          /// <summary>
          ///     Whether the prototyped func was generated by an anonymous view
          ///     ({| ? |}) assertion.
          /// </summary>
          IsAnonymous : bool }

    /// <summary>
    ///     Record of a sanity check that has been postponed to the backend due
    ///     to missing information.
    ///
    ///     <para>
    ///         Starling tries to check certain aspects of a proof for sanity
    ///         before handing off to a backend, but sometimes there is
    ///         information missing that the backend itself can give.  In these
    ///         cases, it forces the backend to add the check as a proof term,
    ///         which offers less immediate 'your proof is wrong' feedback but
    ///         ensures as many proofs as possible are sound.
    ///     </para>
    /// </summary>
    type DeferredCheck =
        /// <summary>
        ///     The given iterated func needs its definition checking for base
        ///     downclosure.
        /// </summary>
        | NeedsBaseDownclosure of func : IteratedDFunc * why : string
        /// <summary>
        ///     The given iterated func needs its definition checking for
        ///     inductive downclosure.
        /// </summary>
        | NeedsInductiveDownclosure of func : IteratedDFunc * why : string

    (*
     * Models
     *)

    /// A parameterised model of a Starling program.
    type Model<'axiom, 'viewdefs> =
        { /// <summary>
          ///     The shared variable environment.
          /// </summary>
          SharedVars : VarMap
          /// <summary>
          ///     The thread-local variable environment.
          /// </summary>
          ThreadVars : VarMap
          /// <summary>
          ///     The set of proof terms in the model.
          /// </summary>
          Axioms : Map<string, 'axiom>
          /// <summary>
          ///     The semantic function for this model.
          /// </summary>
          Semantics : PrimSemanticsMap
          /// <summary>
          ///     This corresponds to the function D.
          /// </summary>
          ViewDefs : 'viewdefs
          /// <summary>
          ///     The view prototypes defined in this model.
          /// </summary>
          ViewProtos : FuncDefiner<ProtoInfo>
          /// <summary>
          ///     A log of any deferred checks the backend must do.
          /// </summary>
          DeferredChecks : DeferredCheck list }


/// <summary>
///     Pretty printers for the model.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Command.Pretty

    /// Pretty-prints a term, given printers for its commands and views.
    let printTerm
      (pCmd : 'Cmd -> Doc)
      (pWPre : 'WPre -> Doc)
      (pGoal : 'Goal -> Doc)
      ({Cmd = c; WPre = w; Goal = g} : Term<'Cmd, 'WPre, 'Goal>)
      : Doc =
        vsep [ headed "Command" (c |> pCmd |> Seq.singleton)
               headed "W/Prec" (w |> pWPre |> Seq.singleton)
               headed "Goal" (g |> pGoal |> Seq.singleton) ]

    /// Pretty-prints an STerm.
    let printSTerm
      (pWPre : 'WPre -> Doc)
      (pGoal : 'Goal -> Doc)
      : STerm<'WPre, 'Goal> -> Doc =
        printTerm printSMBoolExpr pWPre pGoal

    /// <summary>
    ///     Pretty-prints an uninterpreted symbol.
    /// </summary>
    /// <param name="s">
    ///     The value of the symbol.
    /// </param>
    /// <returns>
    ///     A command printing <c>%{s}</c>.
    /// </returns>
    let printSymbol (s : string) : Doc =
        hjoin [ String "%" ; s |> String |> braced ]

    /// Pretty-prints the axiom map for a model.
    let printModelAxioms
      (pAxiom : 'Axiom -> Doc)
      (model : Model<'Axiom, _>)
      : Doc =
        printMap Indented String pAxiom model.Axioms

    /// <summary>
    ///     Pretty-prints a deferred check.
    /// </summary>
    /// <param name="check">The deferred check to print.</param>
    /// <returns>A <see cref="Doc"/> capturing the deferred check.</returns>
    let printDeferredCheck (check : DeferredCheck) : Doc =
        warning <|
            match check with
            | NeedsBaseDownclosure (func, why) ->
                colonSep
                    [ String "base downclosure check for iterated func"
                        <+> printIteratedDFunc func
                      String why ]
            | NeedsInductiveDownclosure (func, why) ->
                colonSep
                    [ hsep
                        [ String "inductive downclosure check for iterated func"
                            <+> printIteratedDFunc func ]
                      String why ]

    /// Pretty-prints a model given axiom and defining-view printers.
    let printModel
      (pAxiom : 'Axiom -> Doc)
      (pDefiner : 'Definer -> Doc seq)
      (model : Model<'Axiom, 'Definer>)
      : Doc =
        headed "Model"
            [ headed "Shared variables" <|
                  Seq.singleton
                      (printMap Inline String printType model.SharedVars)
              headed "Thread variables" <|
                  Seq.singleton
                      (printMap Inline String printType model.ThreadVars)
              headed "ViewDefs" <|
                  pDefiner model.ViewDefs
              headed "Axioms" <|
                  Seq.singleton (printModelAxioms pAxiom model)
              headed "Deferred checks" <|
                  Seq.map printDeferredCheck model.DeferredChecks ]

    /// <summary>
    ///     Pretty-prints <see cref="FuncDefiner"/>s.
    /// </summary>
    /// <param name="pDefn">
    ///     Pretty printer for definitions.
    /// </param>
    /// <param name="ft">
    ///     The definer to print.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of definitions in the definer.
    /// </typeparam>
    /// <returns>
    ///     A sequence of <see cref="Doc"/> representing the
    ///     pretty-printed form of <paramref name="ft"/>.
    /// </returns>
    let printFuncDefiner
      (pDefn : 'defn -> Doc)
      (ft : FuncDefiner<'defn>)
      : Doc seq =
        ft
        |> List.map (fun (v, d) -> colonSep [ printDFunc v; pDefn d ] )
        |> List.toSeq

    /// <summary>
    ///     Pretty-prints <see cref="ViewDefiner"/>s.
    /// </summary>
    /// <param name="pDefn">
    ///     Pretty printer for definitions.
    /// </param>
    /// <param name="ft">
    ///     The definer to print.
    /// </param>
    /// <typeparam name="defn">
    ///     The type of definitions in the definer.
    /// </typeparam>
    /// <returns>
    ///     A sequence of <see cref="Doc"/> representing the
    ///     pretty-printed form of <paramref name="ft"/>.
    /// </returns>
    let printViewDefiner
      (pDefn : 'defn -> Doc)
      (ft : ViewDefiner<'defn>)
      : Doc seq =
        ft
        |> List.map (fun (v, d) -> colonSep [ printDView v; pDefn d ] )
        |> List.toSeq

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
    /// <param name="pAxiom">
    ///     The printer to use for model axioms.
    /// </param>
    /// <param name="pDefiner">
    ///     The printer to use for view definitions.
    /// </param>
    /// <param name="mview">
    ///     The <c>ModelView</c> stating which part of the model should be
    ///     printed.
    /// </param>
    /// <param name="model">
    ///     The model to print.
    /// </param>
    /// <typeparam name="Axiom">
    ///     The type of axioms in the model.
    /// </typeparam>
    /// <typeparam name="Definer">
    ///     The type of the view definer in the model.
    /// </typeparam>
    /// <returns>
    ///     A pretty-printer command printing the part of
    ///     <paramref name="model" /> specified by
    ///     <paramref name="mView" />.
    /// </returns>
    let printModelView
      (pAxiom : 'Axiom -> Doc)
      (pDefiner : 'Definer -> Doc seq)
      (mView : ModelView)
      (m : Model<'Axiom, 'Definer>)
      : Doc =
        match mView with
        | ModelView.Model -> printModel pAxiom pDefiner m
        | ModelView.Terms -> printModelAxioms pAxiom m
        | ModelView.Term termstr ->
            maybe (termstr |> sprintf "no term '%s'" |> String) pAxiom
                (Map.tryFind termstr m.Axioms)


    /// Prints a Term<CommandSemantics, 'WPre, 'Goal> using the WPre and Goal printers provided
    let printCmdTerm pSemantics pWPre pGoal =
        printTerm (printCommandSemantics pSemantics) pWPre pGoal

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
let dfunc (name : string) (pars : TypedVar seq) : DFunc = func name pars

/// <summary>
///     Type-constrained version of <c>func</c> for <c>VFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>VFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>VFunc</c>, as a sequence.
/// </param>
/// <typeparam name="var">
///     The type of variables in the <c>VFunc</c>'s parameters.
/// </typeparam>
/// <returns>
///     A new <c>VFunc</c> with the given name and parameters.
/// </returns>
let vfunc (name : string) (pars : Expr<'var> seq) : VFunc<'var> =
    func name pars

/// <summary>
///     Type-constrained version of <c>vfunc</c> for <c>MVFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>MVFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>MVFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>MVFunc</c> with the given name and parameters.
/// </returns>
let mvfunc (name : string) (pars : MExpr seq) : MVFunc = vfunc name pars

/// <summary>
///     Type-constrained version of <c>vfunc</c> for <c>SVFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>SVFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>SVFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>SVFunc</c> with the given name and parameters.
/// </returns>
let svfunc (name : string) (pars : SVExpr seq) : SVFunc = vfunc name pars

/// <summary>
///     Type-constrained version of <c>vfunc</c> for <c>SMVFunc</c>s.
/// </summary>
/// <param name="name">
///     The name of the <c>SMVFunc</c>.
/// </param>
/// <param name="pars">
///     The parameters of the <c>SMVFunc</c>, as a sequence.
/// </param>
/// <returns>
///     A new <c>SMVFunc</c> with the given name and parameters.
/// </returns>
let smvfunc (name : string) (pars : SMExpr seq) : SMVFunc = vfunc name pars


/// Rewrites a Term by transforming its Cmd with fC, its WPre with fW,
/// and its Goal with fG.
let mapTerm
  (fC : 'SrcCmd -> 'DstCmd)
  (fW : 'SrcWPre -> 'DstWPre)
  (fG : 'SrcGoal -> 'DstGoal)
  ( { Cmd = c; WPre = w; Goal = g } : Term<'SrcCmd, 'SrcWPre, 'SrcGoal> )
  : Term<'DstCmd, 'DstWPre, 'DstGoal> =
    { Cmd = fC c; WPre = fW w; Goal = fG g }

/// Rewrites a Term by transforming its Cmd with fC, its WPre with fW,
/// and its Goal with fG.
/// fC, fW and fG must return Chessie results; liftMapTerm follows suit.
let tryMapTerm
  (fC : 'SrcCmd -> Result<'DstCmd, 'Error>)
  (fW : 'SrcWPre -> Result<'DstWPre, 'Error>)
  (fG : 'SrcGoal -> Result<'DstGoal, 'Error>)
  ({Cmd = c; WPre = w; Goal = g} : Term<'SrcCmd, 'SrcWPre, 'SrcGoal>)
  : Result<Term<'DstCmd, 'DstWPre, 'DstGoal>, 'Error> =
    trial {
        let! cR = fC c;
        let! wR = fW w;
        let! gR = fG g;
        return {Cmd = cR; WPre = wR; Goal = gR}
    }

/// Returns the axioms of a model.
let axioms ({Axioms = xs} : Model<'Axiom, _>) : Map<string, 'Axiom> = xs

/// Creates a new model that is the input model with a different axiom set.
/// The axiom set may be of a different type.
let withAxioms (xs : Map<string, 'y>) (model : Model<'x, 'dview>)
    : Model<'y, 'dview> =
    { SharedVars = model.SharedVars
      ThreadVars = model.ThreadVars
      ViewDefs = model.ViewDefs
      Semantics = model.Semantics
      Axioms = xs
      ViewProtos = model.ViewProtos
      DeferredChecks = model.DeferredChecks }

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

/// Returns the viewdefs of a model.
let viewDefs ({ViewDefs = ds} : Model<_, 'Definer>) : 'Definer = ds

/// Creates a new model that is the input model with a different viewdef set.
/// The viewdef set may be of a different type.
let withViewDefs (ds : 'Definer2)
                 (model : Model<'Axiom, 'Definer1>)
                 : Model<'Axiom, 'Definer2> =
    { SharedVars = model.SharedVars
      ThreadVars = model.ThreadVars
      ViewDefs = ds
      Semantics = model.Semantics
      Axioms = model.Axioms
      ViewProtos = model.ViewProtos
      DeferredChecks = model.DeferredChecks }

/// Maps a pure function f over the viewdef database of a model.
let mapViewDefs (f : 'x -> 'y) (model : Model<'axiom, 'x>) : Model<'axiom, 'y> =
    withViewDefs (model |> viewDefs |> f) model

/// Maps a failing function f over the viewdef database of a model.
let tryMapViewDefs (f : 'x -> Result<'y, 'e>) (model : Model<'axiom, 'x>)
    : Result<Model<'axiom, 'y>, 'e> =
    lift (fun x -> withViewDefs x model) (model |> viewDefs |> f)
