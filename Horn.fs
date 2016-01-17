/// Types and backend for emitting Horn clauses for HSF consumption.
module Starling.Horn

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Var
open Starling.Expr
open Starling.Model
open Starling.Reifier
open Starling.Errors.Horn

/// A literal in a Datalog-style Horn clause.
/// We model Datalog terms as Starling expressions, refusing those
/// expressions not modellable in Datalog at output time.
/// Only arithmetic expressions can be modelled in HSF, so we disallow
/// Booleans.
type Literal = 
    /// A predicate.
    | Pred of Func<ArithExpr>
    | And of Literal list
    | Or of Literal list
    | True
    | False
    | ITE of Literal * Literal * Literal
    | Eq of ArithExpr * ArithExpr
    | Neq of ArithExpr * ArithExpr
    | Gt of ArithExpr * ArithExpr
    | Ge of ArithExpr * ArithExpr
    | Le of ArithExpr * ArithExpr
    | Lt of ArithExpr * ArithExpr

/// A Horn clause, in Datalog form.
type Horn = 
    { /// The head of a Horn clause.
      Head : Literal
      /// The body of a Horn clause.
      Body : Literal list }

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

/// Checks whether an ArithExpr is useable by HSF.
let checkArith =
    function
    | AAdd [] -> EmptyCompoundExpr "addition" |> fail
    | ASub [] -> EmptyCompoundExpr "subtraction" |> fail
    | AMul [] -> EmptyCompoundExpr "multiplication" |> fail
    | x -> ok x

/// Converts a BoolExpr to a HSF literal.
let rec boolExpr =
    function
    // TODO(CaptainHayashi): are these allowed?
    | BAnd xs -> List.map boolExpr xs |> collect |> lift And
    | BOr xs -> List.map boolExpr xs |> collect |> lift Or
    | BTrue -> ok <| True
    | BFalse -> ok <| False
    | BEq(AExpr x, AExpr y) -> lift2 (curry Eq) (checkArith x) (checkArith y)
    | BNot(BEq(AExpr x, AExpr y)) -> lift2 (curry Neq) (checkArith x) (checkArith y)
    | BGt(x, y) -> lift2 (curry Gt) (checkArith x) (checkArith y)
    | BGe(x, y) -> lift2 (curry Ge) (checkArith x) (checkArith y)
    | BLe(x, y) -> lift2 (curry Le) (checkArith x) (checkArith y)
    | BLt(x, y) -> lift2 (curry Lt) (checkArith x) (checkArith y)
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
/// Takes the number of globals, as added to each multiset func by GlobalAdd, to
/// remove for each item past the first.
let paramsInMultiset nglobals ms =
    (* Why is this sound?
     * Because GlobalAdd always adds in the globals list at the front of each
     * multiset, and it will contain all of the globals in env.  Thus, if the
     * env is n items, the first n parameters are surplus to requirements.
     *
     * TODO(CaptainHayashi): find a more elegant solution to the problem of
     * collating the global parameters on views.
     *)
    let mseq = ms |> Multiset.toSeq

    let globals =
        mseq
        |> Seq.truncate 1
        |> Seq.map (fun v -> v.Params |> Seq.take nglobals)
        |> Seq.concat

    let rest =
        mseq
        |> Seq.map (fun v -> v.Params |> Seq.skip nglobals)
        |> Seq.concat

    Seq.append globals rest


/// Ensures a param in a viewdef multiset is arithmetic.
let ensureArith =
   function
   | (Type.Int, x) -> ok (aUnmarked x)
   | x -> fail <| NonArithParam x

(*
 * View definitions
 *)

/// Constructs a pred from a multiset, given a set of active globals,
/// and some transformer from the parameters to expressions.
let predOfMultiset gs parT ms =
    lift (fun parR ->
          Pred { Name = predNameOfMultiset ms; Params = parR })
         (ms |> paramsInMultiset (gs |> Map.toSeq |> Seq.length) |> Seq.map parT |> collect)

/// Constructs a full constraint in HSF.
/// The map of active globals should be passed as gs.
/// Some is returned if the constraint is definite; None otherwise.
let hsfConstraint gs { CViews = vs; CExpr = ex } =
    Option.map (fun dex ->
        lift2 (fun hd bd ->
            { Head = hd
              Body = [ bd ] }) (boolExpr dex) (predOfMultiset gs ensureArith vs)) ex

/// Constructs a set of Horn clauses for all definite viewdefs in a model.
let hsfModelViewDefs gs =
    Seq.choose (hsfConstraint gs)
    >> collect
    >> lift Set.ofSeq

(*
 * Variables
 *)

/// Constructs a Horn clause for initialising an integer variable.
/// Returns an error if the variable is not an integer.
/// Returns no clause if the variable is not initialised.
/// Takes the environment of active global variables.
let hsfModelVariables gs =
    let vpars =
        gs
        |> Map.toSeq
        |> Seq.map
            (fun (name, ty) ->
             match ty with
             | Type.Int -> aUnmarked name |> ok
             | _ -> NonArithVar (ty, name) |> fail)
        |> collect

    let head = 
        bind
            (fun vp -> predOfMultiset
                           gs
                           ok
                           (Multiset.singleton { Name = "emp"; Params = vp }))
            vpars


    // TODO(CaptainHayashi): actually get these initialisations from
    // somewhere instead of assuming everything to be 0L.
    lift2 (fun hd vp -> { Head = hd
                          Body = List.map (fun n -> Eq (n, AInt 0L)) vp })
          head
          vpars

(*
 * Terms
 *)

/// Converts a top-level Boolean expression to a list of Horn literals.
let topLevelExpr =
    // The main difference here is that we model conjunctions directly as a
    // Horn literal list.
    function
    | BAnd xs -> xs |> Seq.ofList |> Seq.filter (isTrue >> not)
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
let hsfGuarMultiset dvs env { Cond = c; Item = ms } =
    // We check the defining views here, because anything not in the
    // defining views is to be held true.
    match (findDefOfView dvs ms) with
        | Some _ ->
            Some (lift2 (fun cR msR -> ite cR msR True)
                    (boolExpr c)
                    (predOfMultiset env tryArithExpr ms))
        | None -> None

/// Constructs the body for a set of condition pair Horn clauses,
/// given the defining views, preconditions and semantics clause.
let hsfConditionBody dvs env ps sem =
    let psH =
        ps
        |> Multiset.toSeq
        |> Seq.choose (hsfGuarMultiset dvs env)
        |> collect
        |> lift List.ofSeq

    let semH = topLevelExpr sem

    lift2 List.append psH semH

/// Constructs a single Horn clause given its body, postcondition, and
/// command semantics, as well as a globals environment.
let hsfConditionSingle dvs env q body =
    lift (fun qH -> { Head = qH ; Body = body })
         (Option.get (hsfGuarMultiset dvs env q))

/// Constructs a series of Horn clauses for a term.
/// Takes the environment of active global variables.
let hsfTerm dvs env {Conditions = {Pre = ps ; Post = qs} ; Inner = sem} =
    let body = hsfConditionBody dvs env ps sem

    // Each postcondition generates a new clause.
    qs
    |> Multiset.toSeq
    |> Seq.map (fun q -> bind (hsfConditionSingle dvs env q) body) 
    |> collect

/// Constructs a set of Horn clauses for all terms associated with a model.
let hsfModelAxioms gs dvs =
    Seq.map (hsfTerm dvs gs)
    >> collect
    >> lift Seq.concat

/// Constructs a HSF script for a model.
let hsfModel { Globals = gs; DefViews = dvs; Axioms = xs } =
    trial {
        let! vs = gs |> hsfModelVariables |> lift Seq.singleton
        let! ds = hsfModelViewDefs gs dvs |> lift Set.toSeq
        let! xs = hsfModelAxioms gs dvs xs
        return Seq.concat [vs; ds; xs] |> List.ofSeq
    }