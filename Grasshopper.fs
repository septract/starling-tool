/// <summary>
///     Backend for emitting verification conditions in Grasshopper format
/// </summary>
module Starling.Backends.Grasshopper 

open Chessie.ErrorHandling

open Starling
open Starling.Collections
open Starling.Utils
open Starling.Core.Command
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Semantics
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Instantiate
open Starling.Core.GuardedView
open Starling.Core.Traversal
open Starling.Backends.Z3
open Starling.Optimiser.Graph

[<AutoOpen>] 
module Types =
    /// <summary>A Grasshopper variable shadowing a Starling variable.</summary>
    type ShadowVar =
        { /// <summary>The original Starling variable.</summary>
          Original : MarkedVar }

    /// <summary>A Grasshopper variable.</summary>
    type GrassVar =
        | /// <summary>A Starling variable.</summary>
          Starling of MarkedVar
        | /// <summary>A shadow variable.</summary>
          Shadow of ShadowVar

    /// <summary>A primitive Grasshopper command.</summary>
    type GrassPrim =
        // Shallow encoding!
        Symbolic<Expr<Sym<MarkedVar>>>

    /// <summary>A Grasshopper procedure command.</summary>
    type GrassCommand =
        | /// <summary>A variable declaration.</summary>
          VarDecl of var : CTyped<ShadowVar>
        | /// <summary>A command with no assignment.</summary>
          NoAssign of prim : GrassPrim
        | /// <summary>A command with an assignment to a shadow variable.
          Assign of lvalue : ShadowVar * prim : GrassPrim
        | /// <summary>A pure assumption.</summary>
          PureAssume of assumption : BoolExpr<Sym<GrassVar>>

    /// <summary>A Grasshopper spatial Boolean expression.</summary>
    type Spatial =
        // TODO(CaptainHayashi): don't stringly type strue.
        | /// <summary>A pure expression with a spatial true.</summary>
          Pure of strue : string * body : BoolExpr<MarkedVar>
        | /// <summary>A spatial conjunction.</summary>
          SAnd of l : Spatial * r : Spatial
        | /// <summary>A spatial fact, encoded as a symbol.</summary>
          SFact of Symbolic<Expr<Sym<MarkedVar>>>
        | /// <summary>An implication.</summary>
          SImpl of body : BoolExpr<MarkedVar> * head : Spatial
        | /// <summary>A lone spatial true.</summary>
          STrue of strue : string

    /// <summary>A Grasshopper formula.</summary>
    type Formula =
        // TODO(CaptainHayashi): don't stringly type footprint.
        | /// <summary>A formula with no footprint.</summary>
          NoFootprint of body : Spatial
        | /// <summary>A formula with a footprint.</summary>
          Footprint of spec : string * body : Spatial

    /// <summary>A Grasshopper term (procedure).</summary>
    type GrassTerm =
        { /// <summary>The variable list for this term.</summary>
          Vars : CTyped<MarkedVar> list
          /// <summary>The 'requires' part of the procedure.</summary>
          Requires : Formula
          /// <summary>The 'ensures' part of the procedure.</summary>
          Ensures : Formula
          /// <summary>The command part of the procedure.</summary>
          Commands : GrassCommand list }

    type GrassModel = Model<GrassTerm, FuncDefiner<BoolExpr<Sym<Var>> option>>

    /// <summary>
    ///     Errors raised by the Grasshopper backend.
    /// </summary>
    type Error =
        | /// <summary>
          ///     The given microcode command cannot be expressed in Grasshopper.
          /// </summary>
          CommandNotImplemented of cmd : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
                                 * why : string
        | /// <summary>
          ///     The given expression cannot be expressed in Grasshopper.
          /// </summary>
          ExpressionNotImplemented of expr : Expr<Sym<MarkedVar>>
                                    * why : string
        | /// <summary>
          ///     Some traversal blew up.
          /// </summary>
          Traversal of TraversalError<Error>


module Pretty = 
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Traversal.Pretty
    open Starling.Core.TypeSystem.Pretty

    /// <summary>
    ///     Prints a Grasshopper frontend error.
    /// </summary>
    /// <param name="error">The error to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="error"/>.
    /// </returns>
    let rec printError (error : Error) : Doc =
        match error with
        | CommandNotImplemented (cmd, why) ->
            vsep
                [ cmdHeaded (errorStr "Encountered a command incompatible with Grasshopper")
                    (List.map
                        (printMicrocode
                            (printCTyped printMarkedVar)
                            (printSym printMarkedVar))
                        cmd)
                  errorInfo (String "Reason:" <+> String why) ]
        | ExpressionNotImplemented (expr, why) ->
            vsep
                [ cmdHeaded (errorStr "Encountered an expression incompatible with Grasshopper")
                    [ printExpr (printSym printMarkedVar) expr ]
                  errorInfo (String "Reason:" <+> String why) ]
        | Traversal err -> printTraversalError printError err


    /// Print infix operator across multiple lines
    let infexprV (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc = 
        let mapped = Seq.map pxs xs 
        let resseq = Seq.map (fun x -> vsep [(String op); Indent x]) (Seq.tail mapped) 
        parened (hsep [Seq.head mapped; (hsep resseq)]) 

    /// Print infix operator on one line
    let infexpr (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc = 
        let mapped = Seq.map pxs xs 
        let resseq = Seq.map (fun x -> hsep [(String op); x]) (Seq.tail mapped) 
        parened (hsep [Seq.head mapped; (hsep resseq)]) 

    /// Prints a marked Var 
    let printMarkedVarGrass (v : MarkedVar) : Doc =
        match v with 
        | Before s -> String "before_" <-> String s 
        | After s -> String "after_" <-> String s
        | Intermediate (i, s) -> String "inter_" <-> String (sprintf "%A_" i) <-> String s 
        | Goal (i, s) -> String "goal_" <-> String (sprintf "%A_" i) <-> String s 

    /// <summary>
    ///     Prints a shadow variable.
    /// </summary>
    /// <param name="var">The shadow variable to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="var"/>.
    /// </returns>
    let printShadowVar (var : ShadowVar) : Doc =
        String "shadow_" <-> printMarkedVarGrass var.Original

    /// <summary>
    ///     Prints a general Grasshopper variable.
    /// </summary>
    /// <param name="var">The variable to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="var"/>.
    /// </returns>
    let printGrassVar (var : GrassVar) : Doc =
        match var with
        | Starling stvar -> printMarkedVarGrass stvar
        | Shadow shvar -> printShadowVar shvar

    let printTypedGrass (pVar : 'Var -> Doc) (var : CTyped<'Var>) : Doc = 
        // TODO(CaptainHayashi): is printType correct?
        colonSep [ pVar (valueOf var); Starling.Core.TypeSystem.Pretty.printType (typeOf var)]

    /// Prints a typed Var 
    let printTypedVarGrass (v : TypedVar) : Doc = 
        printTypedGrass String v

    /// Pretty-prints an arithmetic expression.
    let rec printIntExprG (pVar : 'Var -> Doc) (i : IntExpr<'Var>) : Doc =
        match i with
        | IVar c -> pVar c
        | _ -> failwith "[printIntExprG] Case unimplemented for Grasshopper backend." 

    /// Pretty-prints a Boolean expression.
    and printBoolExprG (pVar : 'Var -> Doc) (b : BoolExpr<'Var>) : Doc =
        match b with 
        | BVar c -> pVar c
        | BAnd xs -> infexprV "&&" (printBoolExprG pVar) xs 
        | BOr xs -> infexprV "||" (printBoolExprG pVar) xs
        | BImplies (x, y) -> 
            /// Convert implications to disjunctive form
            printBoolExprG pVar (simp (BOr [BNot x; y])) 
        | BNot (BEq (x, y)) -> infexpr "!=" (printExprG pVar) [x; y]
        | BNot x -> 
            String "!" <+> (printBoolExprG pVar x) |> parened 
        | BEq (x, y) -> infexpr "==" (printExprG pVar) [x; y]
        | BLt (x, y) -> infexpr "<" (stripTypeRec >> printIntExprG pVar) [x; y]
        | BLe (x, y) -> infexpr "<=" (stripTypeRec >> printIntExprG pVar) [x; y]
        | BGe (x, y) -> infexpr ">=" (stripTypeRec >> printIntExprG pVar) [x; y]
        | BGt (x, y) -> infexpr ">" (stripTypeRec >> printIntExprG pVar) [x; y]
        | _ -> failwith "[printBoolExprG] Case unimplemented for Grasshopper backend."
    /// Pretty-prints an expression.
    and printExprG (pVar : 'Var -> Doc) (e : Expr<'Var>) : Doc =
        match e with
        | Int (_, i) -> printIntExprG pVar i
        | Bool (_, b) -> printBoolExprG pVar b
        | _ -> failwith "Unimplemented for Grasshopper backend." 

    let printSymbolicGrass (pArg : 'Arg -> Doc) (s : Symbolic<'Arg>) : Doc =
        let { Sentence = ws; Args = xs } = s
        printInterpolatedSymbolicSentence pArg ws xs

    /// Pretty-prints a symbolic sentence 
    let rec printSymGrass (pReg : 'Var -> Doc) (sym : Sym<'Var>) : Doc =
        match sym with
        | Reg r -> pReg r
        | Sym s -> parened (printSymbolicGrass (printExprG (printSym pReg)) s)

    /// <summary>
    ///     Pretty-prints a Grasshopper primitive command.
    /// </summary>
    /// <param name="prim">The Grasshopper primitive command to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="prim"/>.
    /// </returns>
    let printPrim (prim : GrassPrim) : Doc =
        printSymbolicGrass (printExprG (printSymGrass printMarkedVarGrass)) prim

    /// <summary>
    ///     Pretty-prints a Grasshopper command.
    /// </summary>
    /// <param name="cmd">The Grasshopper command to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="cmd"/>.
    /// </returns>
    let printCommand (cmd : GrassCommand) : Doc =
        let c =
            match cmd with
            | VarDecl var -> String "var" <+> printTypedGrass printShadowVar var
            | NoAssign prim -> printPrim prim
            | Assign (lvalue, prim) ->
                printShadowVar lvalue <+> String ":=" <+> printPrim prim
            | PureAssume assumption ->
                String "pure assume"
                    <+> printBoolExprG (printSymGrass printGrassVar) assumption
        withSemi c

    /// <summary>
    ///     Prints a spatial Boolean expression.
    /// </summary>
    /// <param name="spat">The spatial expression to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="spat"/>.
    /// </returns>
    let rec printSpatial (spat : Spatial) : Doc =
        match spat with
        | Pure (strue, body) ->
            String strue <+> String "&&" <+> printBoolExprG printMarkedVarGrass body
        | SAnd (l, r) ->
            printSpatial l <+> String "&*&" <+> printSpatial r
        | SImpl (l, r) ->
            parened
                ( parened (printBoolExprG printMarkedVarGrass (BNot l))
                  <+> String "||"
                  <+> parened (printSpatial r))
        | SFact f ->
            printSymbolicGrass (printExprG (printSymGrass printMarkedVarGrass)) f
        | STrue strue -> String strue

    /// Print a single Grasshopper query.
    let printGrassTerm (name : string) (term : GrassTerm) : Doc =
        let varprint =
            Indent
                (VSep
                    (Seq.map (printTypedGrass printMarkedVarGrass) term.Vars,
                     String ","))

        /// Print the requires / ensures clauses 
        let reprint expr = 
            match expr with
            | NoFootprint b -> printSpatial b
            | Footprint (spec, b) ->
                String "exists" <+> String spec <+> String "::"
                <+> parened (ivsep [printSpatial b])
        let reqprint = reprint term.Requires
        let ensprint = reprint term.Ensures

        let cmdprint = vsep (List.map printCommand term.Commands)

        vsep [ String "procedure" <+> String name <+> (varprint |> parened) 
               String "requires" 
               Indent reqprint 
               String "ensures" 
               Indent ensprint
               braced (Indent cmdprint)
             ]  

    /// <summary>
    ///     Print a pragma if it has some meaning in GRASShopper.
    /// </summary>
    /// <param name="pragma">The pragma to print.</param>
    /// <returns>
    ///     A document representing the pragma, if it has meaning in
    ///     GRASShopper.
    /// </returns>
    let printPragma (pragma : string * string) : Doc option =
        match pragma with
        | (s, import) when s = "grasshopper_include" ->
            Some
                (String "include \"" <-> String import <-> String "\";")
        | _ -> None

    /// Print all the Grasshopper queries that haven't been eliminated by Z3.
    let printQuery (model: GrassModel) : Doc = 
        let axseq = Map.toSeq model.Axioms
        let tseq = Seq.map (fun (name,term) -> printGrassTerm name term) axseq
        let pragseq = Seq.choose printPragma model.Pragmata 
        let docseq = Seq.append pragseq tseq

        VSep (docseq, VSkip)


/// <summary>
///     Get the set of accessed variables in a term. 
/// </summary>
let findVars (term : Backends.Z3.Types.ZTerm)
  : Result<CTyped<MarkedVar> list, Error> =
    (* For the WPre and Goal, we can just use the symbool representation:
       it's easy to traverse and should be precise.  If we conjoin the two,
       we need only traverse one expression.

       We don't use the symbool for the command, because it has been framed,
       often with variables we don't care about.  Worse, it could have been
       optimised, causing variables we _do_ care about to be lost.  Instead,
       we extract variables out of the microcode. *)
    let goalAndWPre =
        normalBool (mkAnd2 term.SymBool.WPre term.SymBool.Goal)
    let goalAndWPreVarsR =
        findVars (tliftToBoolSrc (tliftToExprDest collectSymVars)) goalAndWPre

    // Remember, traversing a list of lists of microcode!  (Oh the humanity.)
    let cmdVarsT =
        tchainL
            (tchainL
                (traverseMicrocode
                    collectVars
                    (tliftOverExpr collectSymVars))
                id)
            id
    let cmdVarsR =
        findVars cmdVarsT term.Original.Cmd.Microcode

    mapMessages Traversal
        (lift2 (fun gv cv -> Set.toList (Set.union gv cv))
            goalAndWPreVarsR
            cmdVarsR)

/// <summary>
///     Tries to convert a Boolean expression into a spatial expression.
///     <para>
///         This first unfolds all top-level conjunctions, then tries to sort
///         the resulting fact list into spatial and non-spatial parts.
///         If it cannot cleanly separate the two, it fails.
///         The spatial part is then spatially conjoined, and further
///         conjoined to a pure lifting of the non-spatial part.
///     </para>
/// </summary>
/// <param name="strue">
///     The string representing, in Grasshopper syntax, the spatial true used
///     to lift pure observations to spatials.
/// </param>
/// <param name="expr">The Boolean expression to convert.</param>
/// <returns>If successful, the resulting spatial expression.</param>
let rec makeSpatial
  (strue : string)
  (expr : BoolExpr<Sym<MarkedVar>>)
  : Result<Spatial, Error> =
    // TODO(CaptainHayashi): this is probably wrong.

    let partitionSpatial bool (ss, ns) =
        match bool with
        | NoSym n -> ok (ss, n::ns)
        | BImplies (NoSym x, y) ->
            lift
                (fun y' -> (SImpl (x, y')::ss, ns))
                    (makeSpatial strue y)
        | BVar (Sym s) -> ok (SFact s::ss, ns)
        | x ->
            fail
                (ExpressionNotImplemented
                    (expr = normalBoolExpr x,
                     why = "incorrectly mixes spatial and non-spatial parts"))

    let unfolded = unfoldAnds expr
    let partitionedR = seqBind partitionSpatial ([], []) unfolded

    // Optimised conjunction
    let sand x y =
        match (x, y) with
        | (STrue _, s) | (s, STrue _) -> s
        | _ -> SAnd (x, y)

    let combineSpatial spatials nonspatials =
        let cspatials = Seq.fold sand (STrue strue) spatials
        let lifted = Pure (strue, BAnd nonspatials)
        sand lifted cspatials

    lift (uncurry combineSpatial) partitionedR

/// <summary>
///     Tries to convert microcode to Grasshopper commands and ensures.
/// </summary>
/// <param name="routine">The microcode routine to convert.</param>
/// <returns>
///     A Chessie result, containing a list of Grasshopper commands.
/// </returns>
let grassMicrocode (routine : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list list)
  : Result<GrassCommand list, Error> =
    let translateAssign (x, y) =
        maybe BTrue (mkEq (mkVarExp (mapCTyped Reg x))) y

    let grassMicrocodeEntry ent =
        let grassMicrocodeInstruction =
            function
            | Branch _ ->
                fail
                    (CommandNotImplemented
                        (cmd = ent,
                         why = "Cannot encode commands with inner conditionals."))
            | Symbol cmd ->
                // These translate directly into Grasshopper primitive commands.
                ok [ NoAssign cmd ]
            | Microcode.Assign (x, None) ->
                // These only affect framing.
                ok []
            (* We can only translate pure assignments and fully spatial
               (symbolic) assignments. *)
            | Microcode.Assign (x, Some (Int (_, IVar (Sym s))))
            | Microcode.Assign (x, Some (Bool (_, BVar (Sym s))))
            | Microcode.Assign (x, Some (Array (_, AVar (Sym s)))) ->
                (* Fully spatial assignment.
                   Need to create a shadow variable for the command, and use
                   it as a temporary for the assignment itself. *)
                let shadow = { Original = valueOf x }
                let gshadow = Shadow shadow

                let shadowBind =
                    mkEq
                        (mkVarExp (mapCTyped (Starling >> Reg) x))
                        (mkVarExp (withType (typeOf x) (Reg gshadow)))

                ok
                    [ VarDecl (withType (typeOf x) shadow)
                      Assign (shadow, s)
                      PureAssume shadowBind ]
            | Microcode.Assign (x, Some (NoSymE y)) ->
                // Fully pure assignment, turn into pure assume.
                let grassifyR =
                    liftWithoutContext
                        (Starling >> Reg >> ok)
                        (tliftOverCTyped >> tliftOverExpr)
                        y
                let cont grassify =
                    let bind =
                        mkEq
                            (mkVarExp (mapCTyped (Starling >> Reg) x))
                            grassify
                    [ PureAssume bind ]
                lift cont (mapMessages Traversal grassifyR)
            | Microcode.Assign _ ->
                fail
                    (CommandNotImplemented
                        (cmd = ent,
                         why = "Assignments cannot mix symbols and pure expressions."))
            | Assume (NoSym x) ->
                // Pure assumption.
                let grassifyR =
                    liftWithoutContext
                        (Starling >> Reg >> ok)
                        (tliftOverCTyped >> tliftToExprDest >> tliftToBoolSrc)
                        (normalBool x)
                lift (fun x -> [ PureAssume x ]) (mapMessages Traversal grassifyR)
            | Assume _ ->
                fail
                    (CommandNotImplemented
                        (cmd = ent,
                         why = "Impure assumptions not yet supported."))

        lift List.concat (collect (List.map grassMicrocodeInstruction ent))
    lift List.concat (collect (List.map grassMicrocodeEntry routine))

/// <summary>
///     Generates pure assumptions for the Starling variable frame associated
///     with a given state assignment map.
///     <para>
///         Because Grasshopper procedures are quantified by a subset of the
///         Starling variable state, we don't emit framing predicates for
///         variables not mentioned in the term being framed.
///     </para>
/// </summary>
/// <param name="assignMap">The map to convert to a frame.</param>
/// <param name="vars">The set of variables mentioned in the term.</param>
/// <returns>
///     If all went well, a list of Grasshopper commands pure-assuming the
///     variable frame.
/// </returns>
let grassFrame
  (assignMap : Map<TypedVar, MarkedVar>)
  (vars : Set<Var>)
  : Result<GrassCommand list, Error> =
    // Only frame things we use in the term.
    let isUsed var _ = vars.Contains (valueOf var)
    let strippedMap = Map.filter isUsed assignMap

    // We can just adapt the normal frame generator.
    let normalFrame = makeFrame strippedMap

    let grassify x =
        // Pure assumption.
        let grassifyR =
            liftWithoutContext
                (Starling >> ok)
                (tliftOverSym >> tliftOverCTyped >> tliftToExprDest >> tliftToBoolSrc)
                (normalBool x)
        lift PureAssume (mapMessages Traversal grassifyR)

    collect (List.map grassify normalFrame)

/// <summary>
///     Generates a Grasshopper term.
/// </summary>
/// <param name="strue">The 'spatial true' predicate.</param>
/// <param name="footprint">An optional 'name : type' footprint spec.</param>
/// <param name="term">The term to convert to Grasshopper.</param>
/// <returns>
///     A Chessie result, containing the converted term on success.
/// </returns>
let grassTerm
  (strue : string)
  (footprint : string option)
  (term : Backends.Z3.Types.ZTerm) : Result<GrassTerm, Error> =
    let addFootprint =
        maybe NoFootprint (fun f b -> Footprint (f, b)) footprint

    let requiresR = lift addFootprint (makeSpatial strue term.SymBool.WPre)
    let ensuresR = lift addFootprint (makeSpatial strue term.SymBool.Goal)
    let commandsR = grassMicrocode term.Original.Cmd.Microcode
    let varsR = findVars term
    let frameR =
        bind
            (fun vars ->
                // Only frame for things where we actually _use_ the post-state
                let getAfter =
                    function
                    | WithType (After l, _) -> Some l
                    | _ -> None
                let varSet = Set.ofList (List.choose getAfter vars)
                grassFrame term.Original.Cmd.Assigns varSet)
            varsR
    let framedCommandsR = lift2 (@) commandsR frameR

    lift4
        (fun vars requires ensures commands ->
            { Vars = vars
              Requires = requires
              Ensures = ensures
              Commands = commands } )
        varsR requiresR ensuresR framedCommandsR


/// Generate a grasshopper model (currently doesn't do anything) 
let grassModel (model : Backends.Z3.Types.ZModel) : Result<GrassModel,Error> = 
    let fails = extractFailures model
    let failSeq = Map.toSeq fails

    // Pick out some necessary pragmata.
    // TODO(CaptainHayashi): make these not necessary, somehow.
    let footprint =
        List.tryPick
            (fun (x, y) -> if x = "grasshopper_footprint" then Some y else None)
            model.Pragmata
    let strue' =
        List.tryPick
            (fun (x, y) -> if x = "grasshopper_strue" then Some y else None)
            model.Pragmata
    // TODO(CaptainHayashi): clean this up...
    let strue = withDefault "sTrue()" strue'


    let grassTermPair (name, term) = lift (mkPair name) (grassTerm strue footprint term)
    let grassTermPairsR = collect (Seq.map grassTermPair failSeq)

    let grassTermsR = lift Map.ofSeq grassTermPairsR

    lift (fun terms -> withAxioms terms model) grassTermsR
