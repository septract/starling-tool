module Starling.Pretty.Misc

open Microsoft
open Starling
open Starling.Collections
open Starling.Var
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Model
open Starling.Lang.Modeller
open Starling.Z3.Utils
open Starling.Pretty.Expr
open Starling.Pretty.Lang.AST
open Starling.Pretty.Types

/// Pretty-prints a collated script.
let printCollatedScript (cs: CollatedScript) = 
    VSep([ vsep <| List.map printViewProto cs.VProtos
           vsep <| List.map (uncurry (printScriptVar "global")) cs.Globals
           vsep <| List.map (uncurry (printScriptVar "local")) cs.Locals
           vsep <| List.map printConstraint cs.Constraints
           VSep(List.map printMethod cs.Methods, VSkip) ], (vsep [ VSkip; Separator; Nop ]))

/// Pretty-prints Z3 expressions.
let printZ3Exp (expr : #Z3.Expr) = String(expr.ToString())

/// Pretty-prints a singular view assertion.
let printModelView = printFunc printExpr

/// Pretty-prints a type-name parameter.
let printParam (ty, name) = 
    hsep [ ty |> printType
           name |> String ]

/// Pretty-prints a singular view definition.
let printModelViewDef = printFunc printParam

/// Pretty-prints a view list.
let printViewList pview = 
    Multiset.toList
    >> List.map pview
    >> semiSep

/// Pretty-prints a multiset of views.
let printModelViewList = printViewList printModelView

/// Pretty-prints a multiset of viewdefs.
let printModelViewDefs = printViewList printModelViewDef >> squared


/// Pretty-prints model variables.
let printModelVar (name, ty) = 
    colonSep [ String name
               printType ty ]

/// Pretty-prints a conditional view.
let rec printCondView = 
    function 
    | ITE(i, t, e) -> 
        hsep [ String "if"
               printBoolExpr i
               String "then"
               printCondViewList t
               String "else"
               printCondViewList e ]
    | Func v -> printModelView v

/// Pretty-prints a list of cond-views.
and printCondViewList = printViewList printCondView >> ssurround "[| " "|]"

/// Pretty-prints a guarded item.
let printGuarded pitem {Cond = c; Item = i} = 
    if Expr.isTrue c then pitem i
    else 
        parened (HSep([ printBoolExpr c
                        pitem i ], String "|"))

/// Pretty-prints a guarded view.
let printGuarView = printGuarded printModelView

/// Pretty-prints a list of guar-views.
let printGuarViewList = printViewList printGuarView >> ssurround "<|" "|>"

/// Pretty-prints a reified view.
let printReView = printGuarded printModelViewList >> ssurround "((" "))"

/// Pretty-prints a reified view list.
let printReViewList = printViewList printReView >> ssurround "(|" "|)"

/// Pretty-prints something wrapped in a general condition pair.
let printInConditionPair pcond cpair inner = Surround(pcond cpair.Pre, inner, pcond cpair.Post)

/// Lifts a pretty-printer to optional values.
let printOption pp = 
    function 
    | None -> String "(none)"
    | Some v -> pp v

/// Pretty-prints a load prim.
let printLoadPrim ty dest src mode = 
    hsep [ String("load<" + ty + ">")
           parened (equality (printOption printLValue dest) (hsep [ src |> printLValue
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

/// Pretty-prints a Hoare triple
let printHoare pCond pInner { Conditions = cond; Inner = inner } = 
    printInConditionPair pCond cond (angled (pInner inner))

/// Pretty-prints a model axiom.
let printFlatAxiom = printHoare printCondViewList printPrim

/// Pretty-prints a model axiom.
let printFullAxiom = printHoare printGuarViewList printPrim

/// Pretty-prints a semantically translated axiom.
let printSemAxiom (ax : SemAxiom) = 
    printHoare printGuarViewList (printBoolExpr
                                  >> Indent
                                  >> Seq.singleton
                                  >> Seq.toList
                                  >> vsep) ax

/// Pretty-prints a part-axiom at the given indent level.
let rec printPartAxiom = 
    function 
    | PAAxiom ax -> printFlatAxiom ax
    | PAWhile(isDo, expr, outer, inner) -> 
        vsep [ hsep [ String "begin"
                      String(if isDo then "do-while"
                             else "while")
                      String(expr.ToString()) ]
               printInConditionPair printCondViewList outer (vsep [ String "begin block"
                                                                    ivsep <| List.map printPartAxiom inner.Inner
                                                                    String "end block" ])
               String "end" ]
    | PAITE(expr, outer, inTrue, inFalse) -> 
        vsep [ hsep [ String "begin if"
                      String(expr.ToString()) ]
               printInConditionPair printCondViewList outer (vsep [ String "begin true"
                                                                    ivsep <| List.map printPartAxiom inTrue.Inner
                                                                    String "end true; begin false"
                                                                    ivsep <| List.map printPartAxiom inFalse.Inner
                                                                    String "end false" ])
               String "end" ]

/// Pretty-prints a model constraint.
let printModelConstraint { CViews = vs; CExpr = e } = 
    keyMap [ ("View", printModelViewDefs vs)
             ("Expr", withDefault (String "?") (Option.map printBoolExpr e)) ]

/// Pretty-prints a model view prototype.
let printModelViewProto (vn, vps) = 
    // TODO(CaptainHayashi): this is a bit of a cop-out!
    printViewProto { ViewProto.Name = vn
                     Params = vps }

/// Pretty-prints a model given an axiom printer.
let printModel axpp model = 
    Header("Model", 
           Indent <| VSep([ headed "Globals" <| List.map printModelVar (Map.toList model.Globals)
                            headed "Locals" <| List.map printModelVar (Map.toList model.Locals)
                            headed "Views" <| List.map printModelViewProto (Map.toList model.VProtos)
                            headed "Constraints" <| List.map printModelConstraint model.DefViews
                            headed "Axioms" <| List.map axpp model.Axioms ], vsep [ Nop; Separator; Nop ]))

/// Pretty-prints a model with partially resolved axioms.
let printPartModel = printModel printPartAxiom

/// Pretty-prints a model with flattened but not fully resolved axioms.
let printFlatModel = printModel printFlatAxiom

/// Pretty-prints a model with fully resolved axioms.
let printFullModel = printModel printFullAxiom

/// Pretty-prints a model with semantically translated axioms.
let printSemModel = printModel printSemAxiom

/// Pretty-prints a framed axiom.
let printFramedAxiom ax = 
    vsep [ curry Header "Axiom" <| Indent(printSemAxiom ax.Axiom)
           curry Header "Frame" <| Indent(printGuarViewList ax.Frame) ]

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

/// Pretty-prints a list of framed axioms.
let printFramedAxioms = printNumHeaderedList printFramedAxiom

/// Pretty-prints a generic term.
let printGenTerm pv pi tm = 
    vsep [ curry Header "Action" <| Indent(pi tm.Inner)
           curry Header "Pre" <| Indent(pv tm.Conditions.Pre)
           curry Header "Post" <| Indent(pv tm.Conditions.Post) ]

/// Pretty-prints an unreified term.
let printTerm = printGenTerm printGuarViewList printBoolExpr

/// Pretty-prints a list of terms.
let printTerms = printNumHeaderedList printTerm

/// Pretty-prints a reified term.
let printReTerm : ReTerm -> Command = printGenTerm printReViewList printBoolExpr

/// Pretty-prints a list of reified terms.
let printReTerms = printNumHeaderedList printReTerm

/// Pretty-prints a Z3-reified term.
let printZTerm : ZTerm -> Command = printGenTerm printZ3Exp printZ3Exp

/// Pretty-prints a list of Z3-reified terms.
let printZTerms = printNumHeaderedList printZTerm

/// Pretty-prints a list of Z3 expressions.
let printZ3Exps : Z3.BoolExpr list -> Command = printNumHeaderedList printZ3Exp

/// Pretty-prints a satisfiability result.
let printSat = 
    function 
    | Z3.Status.SATISFIABLE -> "fail"
    | Z3.Status.UNSATISFIABLE -> "success"
    | _ -> "unknown"
    >> String

/// Pretty-prints a list of satisfiability results.
let printSats = printNumPrecList printSat
