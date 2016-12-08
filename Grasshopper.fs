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
    /// <summary>A Grasshopper term (procedure).</summary>
    type GrassTerm =
        { /// <summary>The variable list for this term.</summary>
          Vars : CTyped<MarkedVar> list
          /// <summary>The 'requires' part of the procedure.</summary>
          Requires : BoolExpr<Sym<MarkedVar>>
          /// <summary>The 'ensures' part of the procedure.</summary>
          Ensures : BoolExpr<Sym<MarkedVar>>
          /// <summary>The command part of the procedure.</summary>
          Commands : Symbolic<Expr<Sym<MarkedVar>>> list }

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

    let printTypedGrass (pVar : 'Var -> Doc) (var : CTyped<'Var>) : Doc = 
        // TODO(CaptainHayashi): is printType correct?
        colonSep [ pVar (valueOf var); Starling.Core.TypeSystem.Pretty.printType (typeOf var)]

    /// Prints a typed Var 
    let printTypedVarGrass (v : TypedVar) : Doc = 
        printTypedGrass String v

    /// Pretty-prints an arithmetic expression.
    let rec printIntExprG (pVar : 'Var -> Doc) : IntExpr<'Var> -> Doc =
        function
        | IVar c -> pVar c
        | _ -> failwith "[printIntExprG] Case unimplemented for Grasshopper backend." 

    /// Pretty-prints a Boolean expression.
    and printBoolExprG (pVar : Sym<MarkedVar> -> Doc) (fr : bool) (b : BoolExpr<Sym<MarkedVar>>) : Doc =
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
    and printExprG (pVar : Sym<MarkedVar> -> Doc) (fr : bool) (e : Expr<Sym<MarkedVar>>) : Doc =
        match e with
        | Int (_, i) -> printIntExprG pVar i
        | Bool (_, b) -> printBoolExprG pVar fr b
        | _ -> failwith "Unimplemented for Grasshopper backend." 

    let printSymbolicGrass (pArg : 'Arg -> Doc) (s : Symbolic<'Arg>) : Doc =
        let { Sentence = ws; Args = xs } = s
        parened (printInterpolatedSymbolicSentence pArg ws xs)

    /// Pretty-prints a symbolic sentence 
    let rec printSymGrass (pReg : MarkedVar -> Doc) (sym : Sym<MarkedVar>) : Doc =
        match sym with
        | Reg r -> pReg r
        | Sym s -> printSymbolicGrass (printExprG (printSym pReg) false) s

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

        // TODO @(septract) print command properly 
        let cmdprint =
            vsep
                (List.map
                    (printSymbolicGrass (printExprG (printSymGrass printMarkedVarGrass) false)
                     >> withSemi)
                    term.Commands)

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
///     A Chessie result, containing a list of symbolic commands over heaps
///     and a Boolean expression over multi-state variable on success.
/// </returns>
let grassMicrocode (routine : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list list)
  : Result<(Symbolic<Expr<Sym<MarkedVar>>> list * BoolExpr<Sym<MarkedVar>>), Error> =
    let translateAssign (x, y) =
        maybe BTrue (mkEq (mkVarExp (mapCTyped Reg x))) y

    let grassMicrocodeEntry ent =
        match partitionMicrocode ent with
        | (_, _, _, x::xs) ->
            fail
                (CommandNotImplemented
                    (cmd = ent,
                     why = "Cannot encode commands with inner conditionals."))
        | (symbols, assigns, assumes, []) ->
            ok
                (symbols,
                 mkAnd (List.map translateAssign assigns @ assumes))

    let entsR = collect (List.map grassMicrocodeEntry routine)
    lift (List.unzip >> pairMap List.concat mkAnd) entsR

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
    let plainEnsuresR = ok term.SymBool.Goal
    let commandsAndCmdEnsuresR = grassMicrocode term.Original.Cmd.Microcode

    let commandsR = lift fst commandsAndCmdEnsuresR
    let ensuresR =
        lift2 (fun (_, cmdEnsures) ensures -> mkAnd2 cmdEnsures ensures)
            commandsAndCmdEnsuresR
            plainEnsuresR

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
