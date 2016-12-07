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
open Starling.Core.Symbolic.Traversal
open Starling.Core.Instantiate
open Starling.Core.GuardedView
open Starling.Core.Traversal
open Starling.Backends.Z3
open Starling.Optimiser.Graph

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

    /// Print a single Grasshopper query from a ZTerm 
    let printZTermGrass (svars : VarMap) 
                        (name : string) 
                        (zterm: Backends.Z3.Types.ZTerm) : Doc =
        let svarprint = VarMap.toTypedVarSeq svars
                        |> Seq.map printTypedVarGrass 
        let varprint = Seq.map (printTypedGrass printMarkedVarGrass) (findVarsGrass zterm) 
                       |> Seq.append svarprint 
                       |> (fun x -> Indent (VSep(x,String ",")))

        /// Print the requires / ensures clauses 
        let wpreprint = zterm.SymBool.WPre 
                        |> printBoolExprG (printSymGrass printMarkedVarGrass) true
        let goalprint = zterm.SymBool.Goal 
                        |> printBoolExprG (printSymGrass printMarkedVarGrass) true

        // TODO @(septract) print command properly 
        let cmdprint =
            let primPrint markL markR prim =
                match prim with
                | SymC { Symbol = sym } ->
                    // TODO(CaptainHayashi): proper Chessie failure.
                    let sym' =
                        { Sentence = sym.Sentence
                          Args = (List.map markR sym.Args) }

                    printSymbolicGrass (printExprG (printSymGrass printMarkedVarGrass) false) sym'
                | Intrinsic (IAssign { LValue = l; RValue = r }) ->
                    // TODO(CaptainHayashi): correct?
                    withSemi
                        (printExprG (printSymGrass printMarkedVarGrass) false (markL (normalIntExpr l))
                         <+> String ":="
                         <+> printExprG (printSymGrass printMarkedVarGrass) false (markR (normalIntExpr r)))
                | Intrinsic (BAssign { LValue = l; RValue = r }) ->
                    // TODO(CaptainHayashi): correct?
                    withSemi
                        (printExprG (printSymGrass printMarkedVarGrass) false (markL (normalBoolExpr l))
                        <+> String ":="
                        <+> printExprG (printSymGrass printMarkedVarGrass) false (markR (normalBoolExpr r)))
                | Stored cmd ->
                    String "/* error: somehow found a stored command! */"

            let rec hasStored cmd =
                let isStored =
                    function
                    | Stored _ -> true
                    | _ -> false
                List.exists isStored cmd

            (* TODO(CaptainHayashi):
               Currently, the command is not marked with pre-and-post-states.
               This means that we have to do this marking ourselves, and we 
               can't easily do this marking soundly with sequential composition.

               For now, we issue a health warning if we spot a sequential
               composition.  This could do with fixing though... somehow. *)
            let hackilyMakeBefore (expr : Expr<Sym<Var>>) : Expr<Sym<MarkedVar>> =
                returnOrFail (before expr)
            let hackilyMakeSymBefore x =
                { Sentence =  x.Sentence
                  Args = (List.map hackilyMakeBefore x.Args) }

            // Can't print a command with any stored components, for now.
            if hasStored zterm.Original.Cmd.Cmd
            then
                // TODO(CaptainHayashi): is this the right fallback?
                vsep
                    [ String "/* WARNING: Given a non-symbolic command, which is unsupported."
                      String "   Boolean translation is below."
                      Indent
                        (printBoolExprG
                            (printSymGrass printMarkedVarGrass)
                            false
                            zterm.SymBool.Cmd)
                      String "   */"
                    ]
            else
                // TODO(CaptainHayashi): fix sequential composition as above.
                match zterm.Original.Cmd.Cmd with
                | [x] ->
                    primPrint (after >> returnOrFail) (before >> returnOrFail) x
                | xs ->
                    vsep
                        [ String "/* WARNING: translation of sequential composition is unsound. */"
                          vsep
                              (List.map
                                (primPrint
                                    (after >> returnOrFail)
                                    (before >> returnOrFail))
                                xs) ]
        vsep [ String "procedure" <+> String name <+> (varprint |> parened) 
               String "requires" 
               Indent wpreprint 
               String "ensures" 
               Indent goalprint
               Indent (braced cmdprint)
             ]  

    /// Print all the Grasshopper queries that haven't been eliminated by Z3.      
    let printQuery (model: GrassModel) : Doc = 
        let fails = extractFailures model 
        Map.toSeq fails 
        |> Seq.map (fun (name,term) -> printZTermGrass model.SharedVars name term) 
        |> (fun x -> (VSep (x,VSkip))) 

    /// Print a Grasshopper error (not implemented yet)
    let printGrassError e = failwith "not implemented yet" 

/// Generate a grasshopper model (currently doesn't do anything) 
let grassModel (i : Backends.Z3.Types.ZModel) : Result<GrassModel,Error>  = 
  ok i 
