/// <summary>
///     Backend for emitting verification conditions in Grasshopper format
/// </summary>
module Starling.Backends.Grasshopper 

open Chessie.ErrorHandling

open Starling 
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Symbolic
open Starling.Core.Instantiate
open Starling.Core.GuardedView

[<AutoOpen>] 
module Types =
    type Grass = Backends.Z3.Types.ZModel // Just piggyback on Z3 for now.  
    type Error = unit 

module Pretty = 
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Symbolic.Pretty

    let printMarkedVar =
        function
        | Before s -> String "before_" <-> String s 
        | After s -> String "after_" <-> String s
        | Intermediate (i, s) -> String "inter_" <-> String (sprintf "%A_" i) <-> String s 
        | Goal (i, s) -> String "goal_" <-> String (sprintf "%A_" i) <-> String s 

    // Print infix operator across multiple lines
    let infexprV (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc = 
        let mapped = Seq.map pxs xs 
        let resseq = Seq.map (fun x -> vsep [(String op); Indent x]) (Seq.tail mapped) 
        hsep [Seq.head mapped; (hsep resseq)] 
        |> parened 

    // Print infix operator on one line
    let infexpr (op : string) (pxs : 'x -> Doc) (xs : seq<'x>) : Doc = 
        let mapped = Seq.map pxs xs 
        let resseq = Seq.map (fun x -> hsep [(String op); x]) (Seq.tail mapped) 
        hsep [Seq.head mapped; (hsep resseq)] 
        |> parened 

    /// Pretty-prints an arithmetic expression.
    let rec printIntExpr (pVar : 'Var -> Doc) : IntExpr<'Var> -> Doc =
        function
        | IVar c -> pVar c
        | _ -> failwith "Unimplemented" 

    /// Pretty-prints a Boolean expression.
    and printBoolExpr (pVar : 'Var -> Doc) : BoolExpr<'Var> -> Doc =
        function
        | BAnd xs -> infexprV "&&" (printBoolExpr pVar) xs
        | BOr xs -> infexprV "||" (printBoolExpr pVar) xs
        | BVar c -> pVar c
        | BImplies (x, y) -> infexprV "==>" (printBoolExpr pVar)  [x; y]
        | BNot (BEq (x, y)) -> infexpr "!=" (printExpr pVar) [x; y]
        | BEq (x, y) -> infexpr "==" (printExpr pVar) [x; y]
        | _ -> failwith "Unimplemented" 

    /// Pretty-prints an expression.
    and printExpr (pVar : 'Var -> Doc) : Expr<'Var> -> Doc =
        function
        | Int i -> printIntExpr pVar i
        | Bool b -> printBoolExpr pVar b
        | _ -> failwith "Unimplemented" 

    let rec printSym (pReg : 'Reg -> Doc) (sym : Sym<'Reg>) : Doc =
        match sym with
        | Reg r -> pReg r
        | Sym { Sentence = ws; Args = xs } ->
            let pArg = printExpr (printSym pReg)
            parened
                (printInterpolatedSymbolicSentence pArg ws xs)

    let printExprGrass a = 
        printBoolExpr (printSym printMarkedVar) a 

    let printQuery (zterm : Backends.Z3.Types.ZTerm) : Doc = 
        headed "Grasshopper terms" <| 
          [ printTerm
              (Core.Expr.Pretty.printBoolExpr (printSym printMarkedVar)) 
              printExprGrass 
              printExprGrass 
              zterm.SymBool ]

    let printGrassError e = 
        failwith "not implemented yet" 

let grassModel (i : Backends.Z3.Types.ZModel) : Result<Grass,Error>  = 
  ok i 
