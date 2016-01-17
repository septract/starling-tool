module Starling.Pretty.Misc

open Microsoft
open Starling
open Starling.Collections
open Starling.Var
open Starling.Lang.Collator
open Starling.Model
open Starling.Z3.Utils
open Starling.Pretty.Expr
open Starling.Pretty.Lang.AST
open Starling.Pretty.Types

(*
 * To separate out
 *)

/// Pretty-prints a list by headering each by its number.
let printNumHeaderedList pp = 
    Seq.ofList
    >> Seq.mapi (fun i x -> Header(sprintf "%d" (i + 1), Indent(pp x)))
    >> Seq.toList
    >> vsep

/// Pretty-prints a list by preceding each by its number.
let printNumPrecList pp = 
    Seq.ofList
    >> Seq.mapi (fun i x -> 
           hsep [ sprintf "%d" (i + 1) |> String
                  pp x ])
    >> Seq.toList
    >> vsep

/// Pretty-prints model variables.
let printModelVar (name, ty) = 
    colonSep [ String name
               printType ty ]


/// Pretty-prints a collated script.
let printCollatedScript (cs: CollatedScript) = 
    VSep([ vsep <| List.map printViewProto cs.VProtos
           vsep <| List.map (uncurry (printScriptVar "global")) cs.Globals
           vsep <| List.map (uncurry (printScriptVar "local")) cs.Locals
           vsep <| List.map printConstraint cs.Constraints
           VSep(List.map printMethod cs.Methods, VSkip) ], (vsep [ VSkip; Separator; Nop ]))

/// Pretty-prints Z3 expressions.
let printZ3Exp (expr : #Z3.Expr) = String(expr.ToString())

/// Pretty-prints a type-name parameter.
let printParam (ty, name) = 
    hsep [ ty |> printType
           name |> String ]

/// Pretty-prints a multiset given a printer for its contents.
let printMultiset pItem = 
    Multiset.toList
    >> List.map pItem
    >> semiSep


/// Pretty-prints a satisfiability result.
let printSat = 
    function 
    | Z3.Status.SATISFIABLE -> "fail"
    | Z3.Status.UNSATISFIABLE -> "success"
    | _ -> "unknown"
    >> String

/// Pretty-prints a list of satisfiability results.
let printSats = printNumPrecList printSat


(*
 * Guards
 *)

/// Pretty-prints a guarded item.
let printGuarded pitem {Cond = c; Item = i} = 
    // Don't bother showing the guard if it's always true.
    if Expr.isTrue c then pitem i
    else 
        parened (HSep([ printBoolExpr c
                        pitem i ], String "|"))


(*
 * Funcs (except Func and CFunc)
 *)

/// Pretty-prints a VFunc.
let printVFunc = printFunc printExpr

/// Pretty-prints a CFunc.
let rec printCFunc = 
    function 
    | ITE(i, t, e) -> 
        hsep [ String "if"
               printBoolExpr i
               String "then"
               t |> printMultiset printCFunc |> ssurround "[ " "]"
               String "else"
               e |> printMultiset printCFunc |> ssurround "[ " "]" ]
    | Func v -> printVFunc v

/// Pretty-prints a guarded view.
let printGFunc = printGuarded printVFunc

/// Pretty-prints a DFunc.
let printDFunc = printFunc printParam


(*
 * Views
 *)

/// Pretty-prints a View.
let printView = printMultiset printVFunc

/// Pretty-prints a DView.
let printDView = printMultiset printDFunc >> squared

/// Pretty-prints a CView.
let printCView = printMultiset printCFunc >> ssurround "[| " "|]"

/// Pretty-prints a GView.
let printGView = printMultiset printGFunc >> ssurround "<|" "|>"

(*
 * View sets
 *)

/// Pretty-prints a view set.
let printViewSet = printMultiset (printGuarded printView >> ssurround "((" "))") >> ssurround "(|" "|)"

/// Pretty-prints something wrapped in a general condition pair.
let printInConds pcond cpair inner = Surround(pcond cpair.Pre, inner, pcond cpair.Post)


(*
 * View definitions
 *)

/// Pretty-prints a model constraint.
let printViewDef { View = vs; Def = e } = 
    keyMap [ ("View", printDView vs)
             ("Def", withDefault (String "?") (Option.map printBoolExpr e)) ]

(*
 * Prims
 *)

/// Pretty-prints a load prim.
let printLoadPrim ty dest src mode = 
    hsep [ String("load<" + ty + ">")
           parened (equality (withDefault (String "(nowhere)")
                                          (Option.map printLValue dest)) (hsep [ src |> printLValue
                                                                                 mode |> printFetchMode ])) ]

/// Pretty-prints a store prim.
let printStorePrim ty dest src = 
    hsep [ String("store<" + ty + ">")
           parened (equality (dest |> printLValue) (src |> printExpr)) ]

/// Pretty-prints a CAS prim.
let printCASPrim ty dest src set = 
    hsep [ String("cas<" + ty + ">")
           parened (commaSep [ dest |> printLValue
                               src |> printLValue
                               set |> printExpr ]) ]

/// Pretty-prints a local-set prim.
let printLocalPrim ty dest src = 
    hsep [ String("lset<" + ty + ">")
           parened (equality (dest |> printLValue) (src |> printExpr)) ]

/// Pretty-prints a prim.
let printPrim = 
    function 
    | IntLoad(dest, src, mode) -> printLoadPrim "arith" dest src mode
    | BoolLoad(dest, src) -> printLoadPrim "bool" (Some dest) src Direct
    | IntStore(dest, src) -> printStorePrim "arith" dest (Expr.AExpr src)
    | BoolStore(dest, src) -> printStorePrim "bool" dest (Expr.BExpr src)
    | IntCAS(dest, src, set) -> printCASPrim "arith" dest src (Expr.AExpr set)
    | BoolCAS(dest, src, set) -> printCASPrim "bool" dest src (Expr.BExpr set)
    | IntLocalSet(dest, src) -> printLocalPrim "arith" dest (Expr.AExpr src)
    | BoolLocalSet(dest, src) -> printLocalPrim "bool" dest (Expr.BExpr src)
    | PrimId -> String "id"
    | PrimAssume expr -> 
        hsep [ String "assume"
               braced (printBoolExpr expr) ]


(*
 * Conds and axioms
 *)

/// Pretty-prints an Axiom, given knowledge of how to print its views
/// and command.
let printAxiom pCmd pView { Conds = conds; Cmd = cmd } = 
    printInConds pView conds (angled (pCmd cmd))

/// Pretty-prints a PAxiom.
let printPAxiom pView = printAxiom printPrim pView

/// Pretty-prints a semantically translated axiom.
let printSAxiom = 
    printAxiom (printBoolExpr
                >> Indent
                >> Seq.singleton
                >> Seq.toList
                >> vsep)

/// Pretty-prints a part-axiom at the given indent level.
let rec printPartAxiom = 
    function 
    | PAAxiom ax -> printPAxiom printCView ax
    | PAWhile(isDo, expr, outer, inner) -> 
        vsep [ hsep [ String "begin"
                      String(if isDo then "do-while"
                             else "while")
                      String(expr.ToString()) ]
               printInConds printCView outer (vsep [ String "begin block"
                                                     ivsep <| List.map printPartAxiom inner.Cmd
                                                     String "end block" ])
               String "end" ]
    | PAITE(expr, outer, inTrue, inFalse) -> 
        vsep [ hsep [ String "begin if"
                      String(expr.ToString()) ]
               printInConds printCView outer (vsep [ String "begin true"
                                                     ivsep <| List.map printPartAxiom inTrue.Cmd
                                                     String "end true; begin false"
                                                     ivsep <| List.map printPartAxiom inFalse.Cmd
                                                     String "end false" ])
               String "end" ]


(*
 * Framed axioms
 *)

/// Pretty-prints a framed axiom.
let printFramedAxiom {Axiom = a; Frame = f} = 
    vsep [ curry Header "Axiom" <| Indent(printSAxiom printGView a)
           curry Header "Frame" <| Indent(printGView f) ]


(*
 * Terms
 *)

/// Pretty-prints a term, given printers for its commands and views.
let printTerm pCmd pView {Cmd = c; WPre = w; Goal = g} = 
    vsep [ curry Header "Command" <| Indent(pCmd c)
           curry Header "W/Prec" <| Indent(pView w)
           curry Header "Goal" <| Indent(pView g) ]

/// Pretty-prints an STerm.
let printSTerm pView = printTerm printBoolExpr pView

(*
 * Models
 *)

/// Pretty-prints a model given an axiom printer.
let printModel pAxiom model = 
    Header("Model", 
           Indent <| VSep([ headed "Globals" <| List.map printModelVar (Map.toList model.Globals)
                            headed "Locals" <| List.map printModelVar (Map.toList model.Locals)
                            headed "ViewDefs" <| List.map printViewDef model.ViewDefs
                            headed "Axioms" <| List.map pAxiom model.Axioms ], vsep [ Nop; Separator; Nop ]))
