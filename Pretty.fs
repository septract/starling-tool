module Starling.Pretty.Misc

open Microsoft
open Starling
open Starling.Collections
open Starling.Var
open Starling.Var.Pretty
open Starling.Lang.Collator
open Starling.Lang.Modeller
open Starling.Core.Model
open Starling.Core.Model.Pretty
open Starling.Pretty.Expr
open Starling.Lang.AST.Pretty
open Starling.Pretty.Types

(*
 * To separate out
 *)

/// Pretty-prints Z3 expressions.
let printZ3Exp (expr : #Z3.Expr) = String(expr.ToString())

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
