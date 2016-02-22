module Starling.Pretty.Misc

open Microsoft
open Starling
open Starling.Collections
open Starling.Var
open Starling.Lang.Collator
open Starling.Model
open Starling.Pretty.Expr
open Starling.Pretty.Lang.AST
open Starling.Pretty.Types

(*
 * To separate out
 *)

/// Pretty-prints a list by headering each by its number.
let printNumHeaderedList pp = 
    Seq.ofList
    >> Seq.mapi (fun i x -> headed (sprintf "%d" (i + 1)) (x |> pp |> Seq.singleton))
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
           vsep <| List.map (uncurry (printScriptVar "shared")) cs.Globals
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
    | CFunc.ITE(i, t, e) -> 
        hsep [ String "if"
               printBoolExpr i
               String "then"
               t |> printMultiset printCFunc |> ssurround "[" "]"
               String "else"
               e |> printMultiset printCFunc |> ssurround "[" "]" ]
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
let printCView = printMultiset printCFunc >> ssurround "[|" "|]"

/// Pretty-prints a GView.
let printGView = printMultiset printGFunc >> ssurround "<|" "|>"


(*
 * View sets
 *)

/// Pretty-prints a view set.
let printViewSet = printMultiset (printGuarded printView >> ssurround "((" "))") >> ssurround "(|" "|)"


(*
 * View definitions
 *)

/// Pretty-prints a model constraint.
let printViewDef pView { View = vs; Def = e } = 
    keyMap [ ("View", pView vs)
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


(*
 * Conds and axioms
 *)

/// Pretty-prints an Axiom, given knowledge of how to print its views
/// and command.
let printAxiom pCmd pView { Pre = pre; Post = post; Cmd = cmd } = 
    Surround(pre |> pView, cmd |> pCmd, post |> pView)

/// Pretty-prints a PAxiom.
let printPAxiom pView = printAxiom printVFunc pView

/// Pretty-prints a semantically translated axiom.
let printSAxiom = 
    printAxiom (printBoolExpr
                >> Indent
                >> Seq.singleton
                >> Seq.toList
                >> vsep)

/// Pretty-prints a part-cmd at the given indent level.
let rec printPartCmd = 
    function 
    | Prim prim -> printVFunc prim
    | While(isDo, expr, inner) -> 
        cmdHeaded (hsep [ String(if isDo then "Do-while" else "While")
                          (printBoolExpr expr) ])
                  (printPartInner inner)
    | ITE(expr, inTrue, inFalse) ->
        cmdHeaded (hsep [String "begin if"
                         (printBoolExpr expr) ])
                  [headed "True" (printPartInner inTrue)
                   headed "False" (printPartInner inFalse)]
/// Prints the inner part of a part command. 
and printPartInner =
    printAxiom (List.map (printAxiom printPartCmd printCView) >> ivsep) printCView
    >> Seq.singleton

(*
 * Framed axioms
 *)

/// Pretty-prints a framed axiom.
let printFramedAxiom {Axiom = a; Frame = f} = 
    vsep [ headed "Axiom" (a |> printSAxiom printGView |> Seq.singleton)
           headed "Frame" (f |> printView |> Seq.singleton) ]


(*
 * Terms
 *)

/// Pretty-prints a term, given printers for its commands and views.
let printTerm pCmd pWPre pGoal {Cmd = c; WPre = w; Goal = g} = 
    vsep [ headed "Command" (c |> pCmd |> Seq.singleton)
           headed "W/Prec" (w |> pWPre |> Seq.singleton)
           headed "Goal" (g |> pGoal |> Seq.singleton) ]

/// Pretty-prints an STerm.
let printSTerm pWPre pGoal = printTerm printBoolExpr pWPre pGoal

(*
 * Models
 *)

/// Pretty-prints a model given axiom and defining-view printers.
let printModel pAxiom pDView model = 
    headed "Model" 
           [ headed "Shared variables" <| List.map printModelVar (Map.toList model.Globals)
             headed "Thread variables" <| List.map printModelVar (Map.toList model.Locals)
             headed "ViewDefs" <| List.map (printViewDef pDView) model.ViewDefs
             headed "Axioms" <| List.map pAxiom model.Axioms ]
