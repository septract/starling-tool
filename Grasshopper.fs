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
open Starling.Core.GuardedView.Traversal
open Starling.Core.View
open Starling.Core.View.Traversal
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

    /// <summary>A Grasshopper formula.</summary>
    type Formula =
        // TODO(CaptainHayashi): don't stringly type footprint.
        { /// <summary>A list of all footprint name-sort pairs.</summary>
          Footprints : (string * string) list
          /// <summary>The body of the formula.</summary>
          Body : BoolExpr<Sym<MarkedVar>> }

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
          ///     The number of footprint names and sorts doesn't match up.
          /// </summary>
          FootprintMismatch
        | /// <summary>
          ///     GRASShopper can't check the given deferred check.
          /// </summary>
          CannotCheckDeferred of check : DeferredCheck * why : string
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
    let rec printError (err : Error) : Doc =
        match err with
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
        | FootprintMismatch -> errorStr "different number of footprint names and sorts"
        | CannotCheckDeferred (check, why) ->
            error
                (String "deferred sanity check '"
                 <-> printDeferredCheck check
                 <-> String "' failed:"
                 <+> String why)
        | Traversal err -> printTraversalError printError err

    /// Print infix operator (generic)
    let infexprG (combine : string -> Doc -> Doc) (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc =
        let mapped = Seq.map pxs xs
        let resseq = Seq.map (combine op) (Seq.tail mapped)
        parened (hsep [Seq.head mapped; (hsep resseq)])

    /// Print infix operator across multiple lines
    let infexprV (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc =
        infexprG (fun o x -> vsep [(String o); Indent x]) op pxs xs

    /// Print infix operator on one line
    let infexpr (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc =
        infexprG (fun o x -> hsep [(String o); x]) op pxs xs

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

    /// <summary>
    ///     Pretty-prints a type using Grasshopper's type names.
    /// </summary>
    let rec printType (ty : Type) : Doc =
        match ty with
        | AnIntR { PrimSubtype = Normal } -> String "Int"
        | ABoolR { PrimSubtype = Normal } -> String "Bool"
        // TODO(CaptainHayashi): is printType correct?
        | x -> Starling.Core.TypeSystem.Pretty.printType x

    let printTypedGrass (pVar : 'Var -> Doc) (var : CTyped<'Var>) : Doc =
        colonSep [ pVar (valueOf var); printType (typeOf var)]

    /// Prints a typed Var
    let printTypedVarGrass (v : TypedVar) : Doc =
        printTypedGrass String v

    /// Pretty-prints an arithmetic expression.
    let rec printIntExprG (pVar : 'Var -> Doc) (i : IntExpr<'Var>) : Doc =
        match i with
        | IVar c -> pVar c
        | IAdd xs -> infexpr "+" (printIntExprG pVar) xs
        | IMul xs -> infexpr "*" (printIntExprG pVar) xs
        | ISub xs -> infexpr "-" (printIntExprG pVar) xs
        | IDiv (x, y) -> infexpr "/" (printIntExprG pVar) [ x ; y ]
        | IMod (x, y) -> infexpr "%" (printIntExprG pVar) [ x ; y ]
        | IInt k -> String (sprintf "%i" k)
        | IIdx _ as x ->
            failwith
                (sprintf
                    "[printIntExprG] Unimplemented for Grasshopper: %A"
                    x)


    /// Pretty-prints a Boolean expression.
    and printBoolExprG (pVar : 'Var -> Doc) (b : BoolExpr<'Var>) : Doc =
        match b with
        | BVar c -> pVar c
        | BTrue -> String "true"
        | BFalse -> String "false"
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
        | x ->
            failwith
                (sprintf
                    "[printBoolExprG] Unimplemented for Grasshopper: %A"
                    x)
    /// Pretty-prints an expression.
    and printExprG (pVar : 'Var -> Doc) (e : Expr<'Var>) : Doc =
        match e with
        | Int (_, i) -> printIntExprG pVar i
        | Bool (_, b) -> printBoolExprG pVar b
        | x ->
            failwith
                (sprintf
                    "[printExprG] Unimplemented for Grasshopper: %A"
                    x)

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

    /// Print a single Grasshopper query.
    let printGrassTerm (name : string) (term : GrassTerm) : Doc =
        let varprint =
            Indent
                (VSep
                    (Seq.map (printTypedGrass printMarkedVarGrass) term.Vars,
                     String ","))

        /// Print the requires / ensures clauses
        let reprint expr =
            let body = printBoolExprG (printSymGrass printMarkedVarGrass) expr.Body
            match expr.Footprints with
            | [] -> body
            | fps ->
                let accs = List.map (fst >> String >> parened >> hsep2 Nop (String "acc")) fps
                let acc = HSep (accs, String " &*& ")

                let pdecl (name, sort) = String name <-> String ":" <-> String sort
                let decls = List.map pdecl fps
                let decl = commaSep decls

                let inner = parened (ivsep [acc <+> String "&*&" ; parened (ivsep [ body ] ) ] )

                String "exists" <+> decl <+> String "::" <+> inner
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
let findTermVars (term : Backends.Z3.Types.ZTerm)
  : Result<CTyped<MarkedVar> list, Error> =
    (* For the WPre and Goal, we used to just use the symbool representation,
       but this can under-approximate the variable accesses if the symbool was
       optimised. *)
    let exprVarsT = tliftOverExpr collectSymVars

    let goalVarsL = findVars (tliftOverFunc exprVarsT) term.Original.Goal
    let wPreVarsL =
        findVars (tchainM (tliftOverGFunc exprVarsT) id) term.Original.WPre

    let goalAndWPreVarsR = lift2 Set.union goalVarsL wPreVarsL

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
            | Assume x ->
                // Pure assumption.
                let grassifyR =
                    liftWithoutContext
                        (Starling >> ok)
                        (tliftOverSym >> tliftOverCTyped >> tliftToExprDest >> tliftToBoolSrc)
                        (normalBool x)
                lift (fun x -> [ PureAssume x ]) (mapMessages Traversal grassifyR)

(*            | Assume (NoSym x) ->
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
                         why = "Impure assumptions not yet supported.")) *)

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
/// <param name="addFoot">Function for adding footprints to Booleans.</param>
/// <param name="term">The term to convert to Grasshopper.</param>
/// <returns>
///     A Chessie result, containing the converted term on success.
/// </returns>
let grassTerm
  (addFoot : BoolExpr<Sym<MarkedVar>> -> Formula)
  (term : Backends.Z3.Types.ZTerm) : Result<GrassTerm, Error> =
    let requires = addFoot term.SymBool.WPre
    let ensures = addFoot term.SymBool.Goal
    let commandsR = grassMicrocode term.Original.Cmd.Microcode
    let varsR = findTermVars term
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

    lift2
        (fun vars commands ->
            { Vars = vars
              Requires = requires
              Ensures = ensures
              Commands = commands } )
        varsR framedCommandsR

/// <summary>
///     Checks the base downclosure property.
///     <para>
///         This states that, for all iterated views <c>A(x)[n]</c>,
///         <c>D(emp) => D(A(x)[0])</c>: their definitions are no stronger
///         than that of the empty view.  If there is no <c>D(emp)</c>, we
///         instead must prove <c>D(A(x)[0])</c> is a tautology.
///     </para>
/// </summary>
/// <param name="definer">The active func definer.</param>
/// <param name="addFoot">Function for adding footprints to Booleans.</param>
/// <param name="func">The iterated func to check, <c>A(x)[n]</c>.</param>
/// <param name="reason">The original reason for the deferred check.</param>
/// <returns>
///     If the base downclosure property can be checked by GRASShopper, a
///     pair of the resulting procedure's name and body; an error otherwise.
/// </returns>
let grassModelBaseDownclosure
  (definer : FuncDefiner<BoolExpr<Sym<Var>> option>)
  (addFoot : BoolExpr<Sym<MarkedVar>> -> Formula)
  (func : IteratedDFunc)
  (reason : string)
  : Result<string * GrassTerm, Error> =
    (* To do the base downclosure, we need to replace all instances of the
       iterator in the definition with 0. *)
    let iteratorR =
        // TODO(CaptainHayashi): subtypes?
        match func.Iterator with
        | Some (Int (_, x)) -> ok x
        | _ ->
            fail
                (CannotCheckDeferred
                    (NeedsBaseDownclosure (func, reason), "malformed iterator"))

    let defnR =
        match FuncDefiner.lookup func.Func definer with
        | Pass (Some (_, Some d)) -> ok d
        | _ ->
            fail
                (CannotCheckDeferred
                    (NeedsBaseDownclosure (func, reason), "func not in definer"))

    let baseDefnR =
        bind2
            (fun i d ->
                mapMessages Traversal
                    (mapOverIteratorUses (fun _ -> IInt 0L) i d))
            iteratorR
            defnR

    // If emp is indefinite (None), we can't check downclosure.
    // TODO(CaptainHayashi): this is pretty grim.
    let empDefn =
        Seq.tryFind
            (fun (dfunc : DFunc, _) -> dfunc.Name = "emp")
            (FuncDefiner.toSeq definer)
    match empDefn with
    | Some (_, Some ed) ->
        (* Base downclosure for a view V[n](x):
             D(emp) => D(V[0](x))
           That is, the definition of V when the iterator is 0 can be no
           stricter than the definition of emp.

           The definition of emp can only mention global variables, so it
           need not need to be freshened. *)
        let mkProc baseDefn =
            (* All of the GRASShopper machinery is expecting the definitions to
               use MarkedVars, but they currently use Vars.  A hacky fix is to
               convert everything to pre-state: *)
            let edBeforeR = beforeBool (normalBool ed)
            let bdBeforeR = beforeBool (normalBool baseDefn)

            let getVars =
                normalBool
                >> findVars (tliftToBoolSrc (tliftToExprDest collectSymVars))
            let empDefnVarsR = bind getVars edBeforeR
            let baseDefnVarsR = bind getVars bdBeforeR
            let varsR = lift2 Set.union empDefnVarsR baseDefnVarsR

            let name = sprintf "%s_base_dc" func.Func.Name

            mapMessages Traversal <| lift3
                (fun vars edBefore bdBefore ->
                    (name,
                     { Vars = Set.toList vars
                       Requires = addFoot edBefore
                       Ensures = addFoot bdBefore
                       Commands = [] } ))
                varsR
                edBeforeR
                bdBeforeR
        bind mkProc baseDefnR
    | _ ->
        fail
            (CannotCheckDeferred
                (NeedsBaseDownclosure (func, reason), "emp is indefinite"))

/// <summary>
///     Checks the inductive downclosure property.
///     <para>
///         This states that, for all iterated views <c>A(x)[n]</c>,
///         for all positive <c>n</c>, <c>D(A(x)[n+1]) => D(A(x)[n])</c>:
///         iterated view definitions must be monotonic over the iterator.
///         This, coupled with base downclosure, allows us to consider only
///         the highest iterator of an iterated func during reification,
///         instead of needing to take all funcs with an iterator less than
///         or equal to it.
///     </para>
/// </summary>
/// <param name="definer">The active func definer.</param>
/// <param name="addFoot">Function for adding footprints to Booleans.</param>
/// <param name="func">The iterated func to check, <c>A(x)[n]</c>.</param>
/// <param name="reason">The original reason for the deferred check.</param>
/// <returns>
///     If the base downclosure property can be checked by GRASShopper, a
///     pair of the resulting procedure's name and body; an error otherwise.
/// </returns>
let grassModelInductiveDownclosure
  (definer : FuncDefiner<BoolExpr<Sym<Var>> option>)
  (addFoot : BoolExpr<Sym<MarkedVar>> -> Formula)
  (func : IteratedDFunc)
  (reason : string)
  : Result<string * GrassTerm, Error> =
    // TODO(CaptainHayashi): de-duplicate this with base DC.
    let iteratorR =
        // TODO(CaptainHayashi): subtypes?
        match func.Iterator with
        | Some (Int (_, x)) -> ok x
        | _ ->
            fail
                (CannotCheckDeferred
                    (NeedsBaseDownclosure (func, reason), "malformed iterator"))

    let baseDefnR =
        match FuncDefiner.lookup func.Func definer with
        | Pass (Some (_, Some d)) -> ok d
        | _ ->
            fail
                (CannotCheckDeferred
                    (NeedsBaseDownclosure (func, reason), "func not in definer"))


    (* To do the inductive downclosure, we need to replace all instances of
       the iterator in the definition with (iterator + 1) in one version. *)
    let succDefnR =
        bind2
            (fun i d ->
                mapMessages Traversal
                    (mapOverIteratorUses (Reg >> incVar) i d))
            iteratorR
            baseDefnR

    (* Inductive downclosure for a view V[n](x):
         (0 <= n && D(V[n+1](x)) => D(V[n](x)))
       That is, the definition of V when the iterator is n+1 implies the
       definition of V when the iterator is n, for all positive n. *)
    let mkProc succDefn baseDefn =
        (* All of the GRASShopper machinery is expecting the definitions to
           use MarkedVars, but they currently use Vars.  A hacky fix is to
           convert everything to pre-state: *)
        let sdBeforeR = beforeBool (normalBool succDefn)
        let bdBeforeR = beforeBool (normalBool baseDefn)

        let getVars =
            normalBool
            >> findVars (tliftToBoolSrc (tliftToExprDest collectSymVars))
        let succDefnVarsR = bind getVars sdBeforeR
        let baseDefnVarsR = bind getVars bdBeforeR
        let varsR = lift2 Set.union succDefnVarsR baseDefnVarsR

        let name = sprintf "%s_ind_dc" func.Func.Name

        mapMessages Traversal <| lift3
            (fun vars sdBefore bdBefore ->
                (name,
                 { Vars = Set.toList vars
                   Requires = addFoot sdBefore
                   Ensures = addFoot bdBefore
                   Commands = [] } ))
            varsR
            sdBeforeR
            bdBeforeR
    bind2 mkProc succDefnR baseDefnR


/// <summary>
///     Converts deferred checks into GRASShopper procedures.
/// </summary>
/// <param name="model">
///     The <see cref="ZModel"/> whose deferred checks are being converted.
/// </param>
/// <returns>
///     Unless a deferred check was found that cannot be modelled, a list of
///     GRASShopper procedures that exercise the given deferred checks.
/// </returns>
let grassModelDeferred
  (model : ZModel)
  (addFoot : BoolExpr<Sym<MarkedVar>> -> Formula)
  : Result<(string * GrassTerm) list, Error> =
    let modelDC =
        function
        | NeedsBaseDownclosure (func, reason) ->
            grassModelBaseDownclosure model.ViewDefs addFoot func reason
        | NeedsInductiveDownclosure (func, reason) ->
            grassModelInductiveDownclosure model.ViewDefs addFoot func reason
    collect (List.map modelDC model.DeferredChecks)

/// <summary>
///     Generate a GRASShopper model.
///     This model contains procedures for each term in the existing model,
///     as well as procedures for deferred checks.
/// </summary>
let grassModel (model : Backends.Z3.Types.ZModel) : Result<GrassModel,Error> =
    let fails = extractFailures model
    let failSeq = Map.toSeq fails

    // Pick out some necessary pragmata.
    // TODO(CaptainHayashi): make these not necessary, somehow.
    let footprintNames =
        List.choose
            (fun (x, y) -> if x = "grasshopper_footprint" then Some y else None)
            model.Pragmata
    let footprintSorts =
        List.choose
            (fun (x, y) -> if x = "grasshopper_footprint_sort" then Some y else None)
            model.Pragmata
    let footprintsR =
        if footprintNames.Length <> footprintSorts.Length
        then fail FootprintMismatch
        else ok (List.zip footprintNames footprintSorts)
    let addFootprintR =
        lift (fun fs b -> { Footprints = fs; Body = b }) footprintsR

    let grassTermsR =
        bind
            (fun addFootprint ->
                let grassTermPair (name, term) =
                    lift (mkPair name) (grassTerm addFootprint term)
                let grassTermPairsR = collect (Seq.map grassTermPair failSeq)
                let dcR = grassModelDeferred model addFootprint

                let unifiedR = lift2 (@) grassTermPairsR dcR
                lift Map.ofSeq unifiedR)
            addFootprintR


    lift (fun terms -> withAxioms terms model) grassTermsR
