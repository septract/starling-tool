/// <summary>
///     Backend for emitting verification conditions in Grasshopper format
/// </summary>
module Starling.Backends.Grasshopper 

open Chessie.ErrorHandling

open Starling
open Starling.Collections
open Starling.Utils
open Starling.Core.Command
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Symbolic
open Starling.Core.Instantiate
open Starling.Core.GuardedView
open Starling.Core.Traversal

[<AutoOpen>] 
module Types =
    type GrassModel = Backends.Z3.Types.ZModel  // Just piggyback on Z3 model.  
    type Error = unit                           // No Grasshopper-specific errors yet. 

module Pretty = 
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Symbolic.Pretty

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

    /// Prints a typed Var 
    let printTypedVarGrass (v : TypedVar) = 
        match v with 
        | Int name -> String name  
        | Bool name -> String name  
        | _ -> failwith "Unimplemented for Grasshopper backend." 

    /// Pretty-prints an arithmetic expression.
    let rec printIntExprG (pVar : 'Var -> Doc) : IntExpr<'Var> -> Doc =
        function
        | IVar c -> pVar c
        | _ -> failwith "Unimplemented for Grasshopper backend." 

    /// Pretty-prints a Boolean expression.
    and printBoolExprG (pVar : 'Var -> Doc) : BoolExpr<'Var> -> Doc =
        function
        | BVar c -> pVar c
        | BAnd xs -> infexprV "&&" (printBoolExprG pVar) xs
        | BOr xs -> infexprV "||" (printBoolExprG pVar) xs
        | BImplies (x, y) -> infexprV "==>" (printBoolExprG pVar)  [x; y]
        | BNot (BEq (x, y)) -> infexpr "!=" (printExprG pVar) [x; y]
        | BEq (x, y) -> infexpr "==" (printExprG pVar) [x; y]
        | BLt (x, y) -> infexpr "<" (printIntExprG pVar) [x; y]
        | BLe (x, y) -> infexpr "<=" (printIntExprG pVar) [x; y]
        | BGe (x, y) -> infexpr ">=" (printIntExprG pVar) [x; y]
        | BGt (x, y) -> infexpr ">" (printIntExprG pVar) [x; y]
        | x -> failwith (sprintf "Unimplemented for Grasshopper backend: %A" x) 

    /// Pretty-prints an expression.
    and printExprG (pVar : 'Var -> Doc) : Expr<'Var> -> Doc =
        function
        | Int i -> printIntExprG pVar i
        | Bool b -> printBoolExprG pVar b
        | _ -> failwith "Unimplemented for Grasshopper backend." 

    let printSymbolicGrass (pArg : 'Arg -> Doc) (s : Symbolic<'Arg>) : Doc =
        let { Sentence = ws; Args = xs } = s
        parened (printInterpolatedSymbolicSentence pArg ws xs)

    /// Pretty-prints a symbolic sentence 
    let rec printSymGrass (pReg : 'Reg -> Doc) (sym : Sym<'Reg>) : Doc =
        match sym with
        | Reg r -> pReg r
        | Sym s -> printSymbolicGrass (printExpr (printSym pReg)) s

    /// Get the set of accessed variables. 
    let findVarsGrass (zterm : Backends.Z3.Types.ZTerm) : seq<MarkedVar> = 
        // TODO @(septract) Should this conjoin the command as well? 
        BAnd [zterm.SymBool.WPre; zterm.SymBool.Goal] 
        |> findVars (tliftToBoolSrc (tliftToExprDest collectSymVars))
        |> lift (Set.map valueOf >> Set.toSeq) 
        |> returnOrFail

    /// Print a single Grasshopper query from a ZTerm 
    let printZTermGrass (svars : VarMap) 
                        (name : string) 
                        (zterm: Backends.Z3.Types.ZTerm) : Doc =

        // TODO @(septract) print variable types
        let svarprint = VarMap.toTypedVarSeq svars
                        |> Seq.map printTypedVarGrass 
        let varprint = Seq.map printMarkedVarGrass (findVarsGrass zterm) 
                       |> Seq.append svarprint 
                       |> (fun x -> VSep(x,String ",")) 
                       |> Indent 

        /// Print the requires / ensures clauses 
        let wpreprint = zterm.SymBool.WPre 
                        |> printBoolExprG (printSymGrass printMarkedVarGrass) 
        let goalprint = zterm.SymBool.Goal 
                        |> printBoolExprG (printSymGrass printMarkedVarGrass) 

        // TODO @(septract) print command properly 
        let cmdprint =
            let rec matchSymC cmd xs =
                match cmd with
                | [] -> Some xs
                | SymC { Symbol = sym }::cmd' -> matchSymC cmd' (sym::xs)
                | _ -> None

            (* TODO(CaptainHayashi):
               Currently, the command is not marked with pre-and-post-states.
               This means that we have to do this marking ourselves, and we 
               can't easily do this marking soundly with sequential composition.

               For now, we issue a health warning if we spot a sequential
               composition.  This could do with fixing though... somehow. *)
            let hackilyPrintVarGrass (v : Var) : Doc =
                printMarkedVarGrass (Before v)

            match matchSymC zterm.Original.Cmd.Cmd [] with
            | Some [x] ->
                  printSymbolicGrass (printExprG (printSymGrass hackilyPrintVarGrass)) x
            | Some xs ->
                vsep
                    [ String "/* WARNING: translation of sequential composition may be unsound. */"
                      (semiSep
                          (List.map
                              (printSymbolicGrass (printExprG (printSymGrass hackilyPrintVarGrass)))
                          xs)) ]
            | None ->
                // TODO(CaptainHayashi): is this the right fallback?
                vsep
                    [ String "/* WARNING: Given a non-symbolic command, which is unsupported."
                      String "   Boolean translation is below."
                      Indent
                        (printBoolExprG
                            (printSymGrass printMarkedVarGrass)
                            zterm.SymBool.Cmd)
                      String "   */"
                    ]
        vsep [ String "procedure" <+> String name <+> (varprint |> parened) 
               String "requires" 
               Indent wpreprint <+> String ";" 
               String "ensures" 
               Indent goalprint <+> String ";" 
               cmdprint 
             ]  

    /// Print all the Grasshopper queries for a model.      
    let printQuery (model: GrassModel) : Doc = 
        Map.toSeq model.Axioms 
        |> Seq.map (fun (name,term) -> printZTermGrass model.SharedVars name term) 
        |> vsep

    /// Print a Grasshopper error (not implemented yet)
    let printGrassError e = failwith "not implemented yet" 

/// Generate a grasshopper model (currently doesn't do anything) 
let grassModel (i : Backends.Z3.Types.ZModel) : Result<GrassModel,Error>  = 
  ok i 
