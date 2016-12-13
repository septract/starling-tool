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

    /// <summary>A Grasshopper term (procedure).</summary>
    type GrassTerm =
        { /// <summary>The variable list for this term.</summary>
          Vars : CTyped<MarkedVar> list
          /// <summary>The 'requires' part of the procedure.</summary>
          Requires : BoolExpr<Sym<MarkedVar>>
          /// <summary>The 'ensures' part of the procedure.</summary>
          Ensures : BoolExpr<Sym<MarkedVar>>
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
    let rec printIntExprG (pVar : Sym<'Var> -> Doc) : IntExpr<Sym<'Var>> -> Doc =
        function
        | IVar c -> pVar c
        | _ -> failwith "[printIntExprG] Case unimplemented for Grasshopper backend." 

    /// Pretty-prints a Boolean expression.
    and printBoolExprG (pVar : Sym<'Var> -> Doc) (fr : bool) (b : BoolExpr<Sym<'Var>>) : Doc =
        match b, fr with 
        | NoSym x, true ->   
           String "sTrue() &*&" <+> printBoolExprG pVar false b |> parened 
        | _ -> 
           match b with 
           | BVar c -> pVar c
           | BAnd xs -> infexprV "&&" (printBoolExprG pVar fr) xs 
           | BOr xs -> infexprV "||" (printBoolExprG pVar fr) xs
           | BImplies (x, y) -> 
               /// Convert implications to disjunctive form
               printBoolExprG pVar fr (simp (BOr [BNot x; y])) 
           | BNot (BEq (x, y)) -> infexpr "!=" (printExprG pVar fr) [x; y]
           | BNot x -> 
              // match x with 
              // | NoSym y -> 
                  String "!" <+> (printBoolExprG pVar fr x) |> parened 
              // | _ -> failwith "[printBoolExprG] Grasshopper can't negate spatial things." 
           | BEq (x, y) -> infexpr "==" (printExprG pVar fr) [x; y]
           | BLt (x, y) -> infexpr "<" (stripTypeRec >> printIntExprG pVar) [x; y]
           | BLe (x, y) -> infexpr "<=" (stripTypeRec >> printIntExprG pVar) [x; y]
           | BGe (x, y) -> infexpr ">=" (stripTypeRec >> printIntExprG pVar) [x; y]
           | BGt (x, y) -> infexpr ">" (stripTypeRec >> printIntExprG pVar) [x; y]
           | _ -> failwith "[printBoolExprG] Case unimplemented for Grasshopper backend."
    /// Pretty-prints an expression.
    and printExprG (pVar : Sym<'Var> -> Doc) (fr : bool) (e : Expr<Sym<'Var>>) : Doc =
        match e with
        | Int (_, i) -> printIntExprG pVar i
        | Bool (_, b) -> printBoolExprG pVar fr b
        | _ -> failwith "Unimplemented for Grasshopper backend." 

    let printSymbolicGrass (pArg : 'Arg -> Doc) (s : Symbolic<'Arg>) : Doc =
        let { Sentence = ws; Args = xs } = s
        parened (printInterpolatedSymbolicSentence pArg ws xs)

    /// Pretty-prints a symbolic sentence 
    let rec printSymGrass (pReg : 'Var -> Doc) (sym : Sym<'Var>) : Doc =
        match sym with
        | Reg r -> pReg r
        | Sym s -> printSymbolicGrass (printExprG (printSym pReg) false) s

    /// <summary>
    ///     Pretty-prints a Grasshopper primitive command.
    /// </summary>
    /// <param name="prim">The Grasshopper primitive command to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="prim"/>.
    /// </returns>
    let printPrim (prim : GrassPrim) : Doc =
        printSymbolicGrass (printExprG (printSymGrass printMarkedVarGrass) false) prim

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
                    <+> printBoolExprG (printSymGrass printGrassVar) false assumption
        withSemi c

    /// Get the set of accessed variables. 
    let findVarsGrass (zterm : Backends.Z3.Types.ZTerm) : CTyped<MarkedVar> seq = 
        normalBool (BAnd [zterm.SymBool.WPre; zterm.SymBool.Goal; zterm.SymBool.Cmd] )
        |> findVars (tliftToBoolSrc (tliftToExprDest collectSymVars)) 
        |> lift Set.toSeq
        |> returnOrFail

    /// Print a single Grasshopper query.
    let printGrassTerm (name : string) (term : GrassTerm) : Doc =
        let varprint =
            Indent
                (VSep
                    (Seq.map (printTypedGrass printMarkedVarGrass) term.Vars,
                     String ","))

        /// Print the requires / ensures clauses 
        let reprint expr = 
            printBoolExprG (printSymGrass printMarkedVarGrass) true expr
        let reqprint = reprint term.Requires
        let ensprint = reprint term.Ensures

        let cmdprint = vsep (List.map printCommand term.Commands)

        vsep [ String "procedure" <+> String name <+> (varprint |> parened) 
               String "requires" 
               Indent reqprint 
               String "ensures" 
               Indent ensprint
               Indent (braced cmdprint)
             ]  

    /// Print all the Grasshopper queries that haven't been eliminated by Z3.
    let printQuery (model: GrassModel) : Doc = 
        let axseq = Map.toSeq model.Axioms
        let docseq =
            Seq.map (fun (name,term) -> printGrassTerm name term) axseq
        VSep (docseq, VSkip)

    /// Print a Grasshopper error (not implemented yet)
    let printGrassError e = failwith "not implemented yet" 

/// <summary>
///     Get the set of accessed local variables in a term. 
/// </summary>
let findVars (term : Backends.Z3.Types.ZTerm)
  : Result<CTyped<MarkedVar> list, Error> =
    (* All of the accessed variables will be in the Boolean
       representation, so just use that. *)
    let fullExpr =
        normalBool (BAnd [term.SymBool.WPre; term.SymBool.Goal; term.SymBool.Cmd])
    let varsR = findVars (tliftToBoolSrc (tliftToExprDest collectSymVars)) fullExpr
    mapMessages Traversal (lift Set.toList varsR)

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
///     Generates a Grasshopper term.
/// </summary>
/// <param name="svars">The map of shared variables in the model.</param>
/// <param name="term">The term to convert to Grasshopper.</param>
/// <returns>
///     A Chessie result, containing the converted term on success.
/// </returns>
let grassTerm
  (term : Backends.Z3.Types.ZTerm) : Result<GrassTerm, Error> =
    let requiresR = ok term.SymBool.WPre
    let ensuresR = ok term.SymBool.Goal
    let commandsR = grassMicrocode term.Original.Cmd.Microcode
    let varsR = findVars term

    lift4
        (fun vars requires ensures commands ->
            { Vars = vars
              Requires = requires
              Ensures = ensures
              Commands = commands } )
        varsR requiresR ensuresR commandsR


/// Generate a grasshopper model (currently doesn't do anything) 
let grassModel (model : Backends.Z3.Types.ZModel) : Result<GrassModel,Error> = 
    let fails = extractFailures model
    let failSeq = Map.toSeq fails

    let grassTermPair (name, term) = lift (mkPair name) (grassTerm term)
    let grassTermPairsR = collect (Seq.map grassTermPair failSeq)

    let grassTermsR = lift Map.ofSeq grassTermPairsR

    lift (fun terms -> withAxioms terms model) grassTermsR
