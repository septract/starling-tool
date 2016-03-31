/// <summary>
///     Backend for emitting Horn clauses for HSF consumption.
/// </summary>
module Starling.Backends.Horn

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.GuardedView
open Starling.Reifier

/// <summary>
///     Types for the Horn clause backend, including errors.
/// </summary>
[<AutoOpen>]
module Types =
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

    /// A Horn clause, in Datalog/HSF form.
    type Horn = 
        /// A normal Horn clause.
        | Clause of head: Literal * body: (Literal list)
        /// A comment.
        | Comment of string
        /// A query-naming call.
        | QueryNaming of Func<string>

    /// An error caused when emitting a Horn clause.
    type Error = 
        /// A viewdef has a non-arithmetic param.
        | NonArithParam of Type * string
        /// A model has a non-arithmetic variable.
        | NonArithVar of Type * string
        /// The expression given is not supported in the given position.
        | UnsupportedExpr of Expr
        /// The expression given is compound, but empty.
        | EmptyCompoundExpr of exptype : string


/// <summary>
///     Pretty printers for the Horn clause generator.
/// </summary>
/// Pretty-prints HSF translation errors.
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Var.Pretty

    /// Emits a constant, munged to work in Datalog.
    let printConst = 
        function 
        | Unmarked c -> sprintf "V%sU" c |> String
        | Before c -> sprintf "V%sB" c |> String
        | After c -> sprintf "V%sA" c |> String
        | Intermediate(i, c) -> sprintf "V%sI%A" c i |> String
        | Goal(i, c) -> sprintf "V%sG%A" c i |> String

    /// Decides whether to put brackets over the expression emission x,
    /// given its expression as the second argument.
    let maybeBracket xe x = 
        match xe with 
        | SimpleArith -> x
        | CompoundArith -> parened x

    /// Emits an arithmetic expression in Datalog syntax.
    let rec printArith = 
        function 
        | AConst c -> printConst c
        | AInt i -> sprintf "%d" i |> String
        // Do some reshuffling of n-ary expressions into binary ones.
        // These expressions are left-associative, so this should be sound.
        | AAdd [] -> failwith "unexpected empty addition"
        | AAdd [ x ] -> printArith x
        | AAdd [ x; y ] -> printBop "+" x y
        | AAdd(x :: y :: xs) -> printArith (AAdd((AAdd [ x; y ]) :: xs))
        | ASub [] -> failwith "unexpected empty subtraction"
        | ASub [ x ] -> printArith x
        | ASub [ x; y ] -> printBop "-" x y
        | ASub(x :: y :: xs) -> printArith (ASub((ASub [ x; y ]) :: xs))
        | AMul [] -> failwith "unexpected empty multiplication"
        | AMul [ x ] -> printArith x
        | AMul [ x; y ] -> printBop "*" x y
        | AMul(x :: y :: xs) -> printArith (AMul((AMul [ x; y ]) :: xs))
        | ADiv(x, y) -> printBop "/" x y

    and printBop op x y =
        binop
            op
            (x |> printArith |> maybeBracket x)
            (y |> printArith |> maybeBracket y)

    /// Emits a Horn literal.
    let rec printLiteral = 
        function 
        | Pred p -> printFunc printArith p
        | And xs ->
            xs
            |> Seq.map printLiteral
            |> commaSep
            |> parened
        | Or xs ->
            xs
            |> Seq.map printLiteral
            |> semiSep
            |> parened
        | ITE (i, t, e) ->
            hsep [ printLiteral i
                   String "->"
                   printLiteral t
                   String ";"
                   printLiteral e ]
            |> parened
        | True -> String "true"
        | False -> String "false"
        | Eq(x, y) -> printBop "=" x y
        | Neq(x, y) -> printBop "=\=" x y
        | Gt(x, y) -> printBop ">" x y
        | Ge(x, y) -> printBop ">=" x y
        | Le(x, y) -> printBop "=<" x y
        | Lt(x, y) -> printBop "<" x y

    /// Emits a Horn clause.
    let printHorn =
        function
        | Clause (hd, bd) ->
            vsep [ hsep [ printLiteral hd
                          String ":-" ]
                   bd |> Seq.map printLiteral |> (fun x -> VSep (x, String ","))
                      |> Indent
                      |> (fun x -> hjoin [x; String "."] ) ]
        | Comment str -> hsep [ String "%"; String str ]
        | QueryNaming {Name = n; Params = ps} ->
            hjoin [ String "query_naming"
                    [ String n
                      ps |> Seq.map String |> commaSep |> squared
                    ]
                    |> commaSep |> parened
                    String "." ]
                           
    /// Emits a Horn clause list.
    let printHorns hs = hs |> List.map printHorn |> vsep
    
    let printHornError =
        function
        | NonArithParam (ty, name) ->
            fmt "parameter '{0}' is of type {1}: HSF only permits integers here"
                [ String name
                  printType ty ]
        | NonArithVar (ty, name) ->
            fmt "variable '{0}' is of type {1}: HSF only permits integers here"
                [ String name
                  printType ty ]
        | UnsupportedExpr expr ->
            fmt "expression '{0}' is not supported in the HSF backend"
                [ printExpr expr ]
        | EmptyCompoundExpr exptype ->
            fmt "found an empty '{0}' expression"
                [ String exptype ]


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
    // TODO(CaptainHayashi): is implies allowed natively?
    | BImplies(x, y) -> boolExpr (mkOr [ mkNot x ; y ])
    | BGt(x, y) -> lift2 (curry Gt) (checkArith x) (checkArith y)
    | BGe(x, y) -> lift2 (curry Ge) (checkArith x) (checkArith y)
    | BLe(x, y) -> lift2 (curry Le) (checkArith x) (checkArith y)
    | BLt(x, y) -> lift2 (curry Lt) (checkArith x) (checkArith y)
    | x -> fail <| UnsupportedExpr(BExpr x)

(*
 * Func sanitisation
 *)

/// Extracts an ArithExpr from an Expr, if it is indeed arithmetic.
/// Fails with UnsupportedExpr if the expresson is Boolean.
let tryArithExpr =
    function
    | AExpr x -> x |> ok
    | e -> e |> UnsupportedExpr |> fail

/// Ensures a param in a viewdef multiset is arithmetic.
let ensureArith =
   function
   | (Type.Int, x) -> ok (aUnmarked x)
   | x -> fail <| NonArithParam x

/// Constructs a pred from a Func, given a set of active globals,
/// and some validator on the parameters.
let predOfFunc gs parT { Name = n; Params = pars } =
    lift (fun parR -> Pred { Name = n; Params = parR })
         (pars |> Seq.map parT |> collect)
(*
 * View definitions
 *)

/// Generates a query_naming clause for a viewdef.
let queryNaming { Name = n; Params = ps } =
    QueryNaming {Name = n; Params = ps |> List.map snd}

/// Constructs a full constraint in HSF.
/// The map of active globals should be passed as gs.
/// Some is returned if the constraint is definite; None otherwise.
let hsfViewDef gs { View = vs; Def = ex } =
    let clause =
        Option.map (fun dex ->
            lift2 (fun hd bd -> [Clause (hd, [bd]); Clause (bd, [hd])])
                  (boolExpr dex)
                  (predOfFunc gs ensureArith vs)) ex
    match clause with
    | Some cl -> lift (fun c -> queryNaming vs :: c) cl
    | None -> ok [ queryNaming vs ]

/// Constructs a set of Horn clauses for all definite viewdefs in a model.
let hsfModelViewDefs gs =
    Seq.map (hsfViewDef gs)
    >> collect
    >> lift (List.concat >> Set.ofSeq)

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
            (fun vp -> predOfFunc
                           gs
                           ok
                           { Name = "emp"; Params = vp })
            vpars


    // TODO(CaptainHayashi): actually get these initialisations from
    // somewhere instead of assuming everything to be 0L.
    lift2 (fun hd vp -> Clause(hd,
                               List.map (fun n -> Eq (n, AInt 0L)) vp ))
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
    | BAnd xs -> xs
    | x -> [x]
    >> List.map boolExpr
    >> collect
    >> lift List.ofSeq

/// Generates an if-then-else, collapsing automatically in the case of true or false.
let ite i t e =
    match i with
    | True -> t
    | False -> e
    | _ -> ITE(i,t,e)

/// Constructs a Horn literal for a Func.
let hsfFunc dvs env func =
    // We check the defining views here, because anything not in the
    // defining views is to be held true.
    // Now that we're at the func level, finding the view is easy!
    List.tryFind (fun {View = {Name = n}} -> n = func.Name) dvs
    |> Option.map (fun _ -> predOfFunc env tryArithExpr func)

/// Constructs a Horn literal for a GFunc.
let hsfGFunc dvs env { Cond = c; Item = ms } =
    hsfFunc dvs env ms
    |> Option.map (lift2 (fun cR msR -> ite cR msR True) (boolExpr c))

/// Constructs the body for a set of condition pair Horn clauses,
/// given the defining views, preconditions and semantics clause.
let hsfConditionBody dvs env ps sem =
    let psH =
        ps
        |> Multiset.toSeq
        |> Seq.choose (hsfGFunc dvs env)
        |> collect
        |> lift List.ofSeq

    let semH = topLevelExpr sem

    lift2 List.append psH semH

/// Constructs a series of Horn clauses for a term.
/// Takes the environment of active global variables.
let hsfTerm dvs env (name, {Cmd = c; WPre = w ; Goal = g}) =
    lift2 (fun head body ->
           [ Comment (sprintf "term %s" name)
             Clause (head, body) ])
          (Option.get (hsfFunc dvs env g))
          (hsfConditionBody dvs env w c)

/// Constructs a set of Horn clauses for all terms associated with a model.
let hsfModelTerms gs dvs =
    Map.toSeq
    >> Seq.map (hsfTerm dvs gs)
    >> collect
    >> lift List.concat

/// Constructs a HSF script for a model.
let hsfModel { Globals = gs; ViewDefs = dvs; Axioms = xs } =
    trial {
        let! vs = gs |> hsfModelVariables
        let! ds = hsfModelViewDefs gs dvs |> lift Set.toList
        let! xs = hsfModelTerms gs dvs xs
        return vs :: List.append ds xs
    }
