/// Backend for emitting Horn clauses for HSF consumption.
module Starling.HSF

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Var
open Starling.Expr
open Starling.Model
open Starling.Horn
open Starling.Errors.Horn

(*
 * Predicate renaming
 *)

/// Generates a predicate name for a view func.
let predNameOfFunc { Name = n } = n.Replace("_", "__")

/// Generates a predicate name for a view multiset.
let predNameOfMultiset ms =
    ms
    |> Multiset.toSeq
    |> Seq.map predNameOfFunc
    |> scons "v"
    |> String.concat "_"

(*
 * Expression generation
 *)

/// Converts a BoolExpr to a HSF literal.
let rec boolExpr =
    function
    // TODO(CaptainHayashi): are these allowed?
    | BAnd xs -> List.map boolExpr xs |> collect |> lift And
    | BOr xs -> List.map boolExpr xs |> collect |> lift Or
    | BTrue -> ok <| True
    | BFalse -> ok <| False
    | BEq(AExpr x, AExpr y) -> ok <| Eq(x, y)
    | BNot(BEq(AExpr x, AExpr y)) -> ok <| Neq(x, y)
    | BGt(x, y) -> ok <| Gt(x, y)
    | BGe(x, y) -> ok <| Ge(x, y)
    | BLe(x, y) -> ok <| Le(x, y)
    | BLt(x, y) -> ok <| Lt(x, y)
    | x -> fail <| UnsupportedExpr(BExpr x)

/// Extracts an ArithExpr from an Expr, if it is indeed arithmetic.
/// Fails with UnsupportedExpr if the expresson is Boolean.
let tryArithExpr =
    function
    | AExpr x -> x |> ok
    | e -> e |> UnsupportedExpr |> fail

(*
 * View def construction
 *)

/// Extracts a sequence all of the parameters in a multiset in order.
let paramsInMultiset ms =
    ms
    |> Multiset.toSeq
    |> Seq.map (fun v -> v.Params)
    |> Seq.concat

/// Ensures a param in a viewdef multiset is arithmetic.
let ensureArith =
   function
   | (Type.Int, x) -> ok (aUnmarked x)
   | x -> fail <| NonArithParam x

(*
 * View definitions
 *)

/// Constructs a pred from a multiset, given a set of active globals,
/// some transformer for the globals to expressions, and some transformer
/// from the parameters to expressions.
let predOfMultiset env envT parT ms =
    lift2 (fun envR parR ->
           Pred { Name = predNameOfMultiset ms
                  Params = List.append envR parR })
          (env |> Set.toSeq |> Seq.map envT |> collect)
          (ms |> paramsInMultiset |> Seq.map parT |> collect)

/// Constructs the right-hand side of a constraint in HSF.
/// The set of active globals should be passed as env.
let bodyOfConstraint env vs =
    predOfMultiset env
                   (aUnmarked >> ok)
                   (ensureArith)
                   vs

/// Constructs a full constraint in HSF.
/// The set of active globals should be passed as env.
/// Some is returned if the constraint is definite; None otherwise.
let hsfConstraint env { CViews = vs; CExpr = ex } =
    Option.map (fun dex ->
        lift2 (fun hd bd ->
            { Head = hd
              Body = [ bd ] }) (boolExpr dex) (bodyOfConstraint env vs)) ex

/// Constructs a set of Horn clauses for all definite viewdefs in a model.
let hsfModelViewDefs { Globals = gs; DefViews = vds } =
    let env = gs |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    vds
    |> Seq.choose (hsfConstraint env)
    |> collect
    |> lift Set.ofSeq

(*
 * Variables
 *)

/// Constructs a Horn clause for initialising an integer variable.
/// Returns an error if the variable is not an integer.
/// Returns no clause if the variable is not initialised.
/// Takes the environment of active global variables.
let hsfVariable env (name, ty) =
    // TODO(CaptainHayashi): actually get these initialisations from
    // somewhere instead of assuming everything to be 0L.
    match ty with
    | Type.Int -> lift (fun hd -> { Head = hd
                                    Body = [Eq (aUnmarked name, AInt 0L)] } )
                       (bodyOfConstraint env (Multiset.empty ()))
                  |> Some
    | _ -> NonArithVar (ty, name) |> fail |> Some

/// Constructs a set of Horn clauses for initialising all integer variables.
/// Returns an error if it detects a non-integer variable.
let hsfModelVariables {Globals = gs} =
    let env = gs |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    gs
    |> Map.toSeq
    |> Seq.choose (hsfVariable env)
    |> collect
    |> lift Set.ofSeq

(*
 * Terms
 *)

/// Converts a condition pair to a pair of 

/// Converts a top-level Boolean expression to a list of Horn literals.
let topLevelExpr =
    // The main difference here is that we model conjunctions directly as a
    // Horn literal list.
    function
    | BAnd xs -> Seq.ofList xs
    | x -> Seq.singleton x
    >> Seq.map boolExpr
    >> collect
    >> lift List.ofSeq

/// Generates an if-then-else, collapsing automatically in the case of true or false.
let ite i t e =
    match i with
    | True -> t
    | False -> e
    | _ -> ITE(i,t,e)

/// Constructs a Horn literal for a guarded view multiset.
let hsfGuarMultiset env marker { Cond = c; Item = ms } =
    lift2 (fun cR msR -> ite cR msR True)
          (boolExpr c)
          (predOfMultiset env (marker >> ok) tryArithExpr ms)

/// Constructs the body for a set of condition pair Horn clauses,
/// given the preconditions and semantics clause.
let hsfConditionBody env ps sem =
    let psH =
        ps
        |> Multiset.toSeq
        |> Seq.map (hsfGuarMultiset env aBefore)
        |> collect
        |> lift List.ofSeq

    let semH = topLevelExpr sem

    lift2 List.append psH semH

/// Constructs a single Horn clause given its body, postcondition, and
/// command semantics, as well as a globals environment.
let hsfConditionSingle env q body =
    lift (fun qH -> { Head = qH ; Body = body })
         (hsfGuarMultiset env aAfter q)

/// Constructs a series of Horn clauses for a term.
/// Takes the environment of active global variables.
let hsfTerm env {Conditions = {Pre = ps ; Post = qs} ; Inner = sem} =
    let body = hsfConditionBody env ps sem

    // Each postcondition generates a new clause.
    qs
    |> Multiset.toSeq
    |> Seq.map (fun q -> bind (hsfConditionSingle env q) body) 
    |> collect

/// Constructs a set of Horn clauses for all terms associated with a model.
let hsfModelAxioms { Globals = gs } xs =
    let env = gs |> Map.toSeq |> Seq.map fst |> Set.ofSeq

    xs
    |> Seq.map (hsfTerm env)
    |> collect
    |> lift Seq.concat

/// Constructs a HSF script for a model.
let hsfModel mdl terms =
    trial {
        let! vs = hsfModelVariables mdl |> lift Set.toSeq
        let! ds = hsfModelViewDefs mdl |> lift Set.toSeq
        let! xs = hsfModelAxioms mdl terms
        return Seq.concat [vs; ds; xs] |> List.ofSeq
    }
