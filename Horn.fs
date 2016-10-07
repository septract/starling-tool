/// <summary>
///     Backend for emitting Horn clauses for HSF consumption.
/// </summary>
module Starling.Backends.Horn

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Semantics
open Starling.Utils
open Starling.Core.Definer
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.View
open Starling.Core.Sub
open Starling.Core.Model
open Starling.Core.Instantiate
open Starling.Core.GuardedView


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
        | Pred of Func<VIntExpr>
        | And of Literal list
        | Or of Literal list
        | True
        | False
        | ITE of Literal * Literal * Literal
        | Eq of VIntExpr * VIntExpr
        | Neq of VIntExpr * VIntExpr
        | Gt of VIntExpr * VIntExpr
        | Ge of VIntExpr * VIntExpr
        | Le of VIntExpr * VIntExpr
        | Lt of VIntExpr * VIntExpr

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
        /// A Func is inconsistent with its definition.
        | InconsistentFunc of func : MVFunc * err : Starling.Core.Definer.Error
        /// A viewdef has a non-arithmetic param.
        | NonArithParam of TypedVar
        /// A model has a non-arithmetic variable.
        | NonArithVar of TypedVar
        /// The expression given is not supported in the given position.
        | UnsupportedExpr of VExpr
        /// The expression given is compound, but empty.
        | EmptyCompoundExpr of exptype : string


/// <summary>
///     Pretty printers for the Horn clause generator.
/// </summary>
/// Pretty-prints HSF translation errors.
module Pretty =
    open Starling.Core.Pretty
    open Starling.Collections.Func.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.Model.Pretty

    /// <summary>
    ///     Given an expression and its Doc, potentially wrap the Doc
    ///     in brackets.
    /// </summary>
    /// <param name="xe">
    ///     The expression for which <paramref name="x"/> is a Doc.
    /// </param>
    /// <param name="x">
    ///     The document form of <paramref name="xe"/>.
    /// </param>
    /// <returns>
    ///     The Doc deriving from potentially bracketing
    ///     <paramref name="x"/>.
    /// </returns>
    let maybeBracket (xe : IntExpr<Var>) (x : Doc) : Doc =
        match xe with
        | SimpleInt -> x
        | CompoundInt -> parened x

    /// Emits an integral expression in Datalog syntax.
    let rec printInt : IntExpr<Var> -> Doc =
        function
        | AVar c -> String c
        | AInt i -> sprintf "%d" i |> String
        // Do some reshuffling of n-ary expressions into binary ones.
        // These expressions are left-associative, so this should be sound.
        | AAdd [] -> failwith "unexpected empty addition"
        | AAdd [ x ] -> printInt x
        | AAdd [ x; y ] -> printBop "+" x y
        | AAdd(x :: y :: xs) -> printInt (AAdd((AAdd [ x; y ]) :: xs))
        | ASub [] -> failwith "unexpected empty subtraction"
        | ASub [ x ] -> printInt x
        | ASub [ x; y ] -> printBop "-" x y
        | ASub(x :: y :: xs) -> printInt (ASub((ASub [ x; y ]) :: xs))
        | AMul [] -> failwith "unexpected empty multiplication"
        | AMul [ x ] -> printInt x
        | AMul [ x; y ] -> printBop "*" x y
        | AMul(x :: y :: xs) -> printInt (AMul((AMul [ x; y ]) :: xs))
        | ADiv(x, y) -> printBop "/" x y

    and printBop (op : string) (x : IntExpr<Var>) (y : IntExpr<Var>) =
        binop
            op
            (x |> printInt |> maybeBracket x)
            (y |> printInt |> maybeBracket y)

    /// Emits a Horn literal.
    let rec printLiteral : Literal -> Doc =
        function
        | Pred p -> printFunc printInt p
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
    let printHorn : Horn -> Doc =
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
    let printHorns (hs : Horn list) : Doc = hs |> List.map printHorn |> vsep

    let printHornError : Error -> Doc =
        function
        | InconsistentFunc (func, err) ->
            wrapped "view func"
                    (printMVFunc func)
                    (Starling.Core.Definer.Pretty.printError err)
        | NonArithParam p ->
            fmt "invalid parameter '{0}': HSF only permits integers here"
                [ printTypedVar p ]
        | NonArithVar p ->
            fmt "invalid variable '{0}': HSF only permits integers here"
                [ printTypedVar p ]
        | UnsupportedExpr expr ->
            fmt "expression '{0}' is not supported in the HSF backend"
                [ printVExpr expr ]
        | EmptyCompoundExpr exptype ->
            fmt "found an empty '{0}' expression"
                [ String exptype ]


(*
 * Expression generation
 *)

/// <summary>
///     Checks whether an <c>IntExpr</c> is useable in HSF, and converts
///     its variables to string form.
/// </summary>
/// <param name="toVar">
///     Converter from variables in the <c>IntExpr</c> to some unique
///     <c>Var</c> representing the variable.  Usually this will be
///     <c>id</c> for <c>VIntExpr</c>s, and <c>unmarkVar</c> for
///     <c>MIntExpr</c>s.
/// </param>
/// <typeparam name="var">
///     The meta-type of variables in the <c>IntExpr</c>.
/// </typeparam>
/// <returns>
///     A function mapping <c>IntExpr</c>s to Chessie-wrapped
///     <c>VIntExpr</c>s.
/// </returns>
let checkArith
  (toVar : 'var -> Var)
  : IntExpr<'var> -> Result<VIntExpr, Error> =
    let rec ca =
        function
        | AVar c -> c |> toVar |> AVar |> ok
        | AInt i -> i |> AInt |> ok
        | AAdd [] -> EmptyCompoundExpr "addition" |> fail
        | ASub [] -> EmptyCompoundExpr "subtraction" |> fail
        | AMul [] -> EmptyCompoundExpr "multiplication" |> fail
        | AAdd xs -> xs |> List.map ca |> collect |> lift AAdd
        | ASub xs -> xs |> List.map ca |> collect |> lift ASub
        | AMul xs -> xs |> List.map ca |> collect |> lift AMul
        | ADiv (x, y) -> lift2 (curry ADiv) (ca x) (ca y)
    ca

/// <summary>
///     Converts a <c>BoolExpr</c> to a HSF literal.
/// </summary>
/// <param name="toVar">
///     Converter from variables in the <c>BoolExpr</c> to some unique
///     <c>Var</c> representing the variable.  Usually this will be
///     <c>id</c> for <c>VBoolExpr</c>s, and <c>unmarkVar</c> for
///     <c>MBoolExpr</c>s.
/// </param>
/// <typeparam name="var">
///     The meta-type of variables in the <c>BoolExpr</c>.
/// </typeparam>
/// <returns>
///     A function mapping <c>BoolExpr</c>s to Chessie-wrapped
///     <c>Literal</c>s.
/// </returns>
let boolExpr
  (toVar : 'var -> Var)
  : BoolExpr<'var> -> Result<Literal, Error> =
    let ca = checkArith toVar

    let rec be =
        function
        // TODO(CaptainHayashi): are these allowed?
        | BAnd xs -> xs |> List.map be |> collect |> lift And
        | BOr xs -> xs |> List.map be |> collect |> lift Or
        | BTrue -> ok <| True
        | BFalse -> ok <| False
        | BEq(Expr.Int x, Expr.Int y) -> lift2 (curry Eq) (ca x) (ca y)
        | BNot(BEq(Expr.Int x, Expr.Int y)) -> lift2 (curry Neq) (ca x) (ca y)
        // TODO(CaptainHayashi): is implies allowed natively?
        | BImplies(x, y) -> be (mkOr [ mkNot x ; y ])
        | BGt(x, y) -> lift2 (curry Gt) (ca x) (ca y)
        | BGe(x, y) -> lift2 (curry Ge) (ca x) (ca y)
        | BLe(x, y) -> lift2 (curry Le) (ca x) (ca y)
        | BLt(x, y) -> lift2 (curry Lt) (ca x) (ca y)
        | x ->
            x
            |> Expr.Bool
            |> Mapper.mapCtx (liftCToSub (Mapper.cmake toVar)) NoCtx
            |> snd
            |> UnsupportedExpr
            |> fail
    be

(*
 * Func sanitisation
 *)

/// <summary>
///     Tries to convert a <c>MExpr</c> to a <c>IntExpr</c>.
///     Fails with <c>UnsupportedExpr</c> if the expression is
///     Boolean.
/// </summary>
let tryIntExpr : MExpr -> Result<IntExpr<Var>, Error> =
    Mapper.mapCtx (liftCToSub (Mapper.cmake unmarkVar)) NoCtx
    >> snd
    >> function
       | Expr.Int x -> ok x
       | e -> e |> UnsupportedExpr |> fail

///<summary>
///     HSF requires variables to start with a capital letter.
///     so we prepend a "V".  This is also done in unmarkVar.
///     @mjp41: TODO: We should consider consolidating this.
///</summary>
let makeHSFVar : string -> string = (+) "V"

/// Ensures a param in a viewdef multiset is arithmetic.
let ensureArith : TypedVar -> Result<IntExpr<Var>, Error> =
    function
    | Int x -> x |> makeHSFVar |> AVar |> ok
    | x -> x |> NonArithParam |> fail

/// Constructs a pred from a Func, given a set of active globals,
/// and some validator on the parameters.
let predOfFunc
  (parT : 'par -> Result<VIntExpr, Error>)
  ({ Name = n; Params = pars } : Func<'par>)
  : Result<Literal, Error> =
    lift (fun parR -> Pred { Name = n; Params = parR })
         (pars |> Seq.map parT |> collect)
(*
 * View definitions
 *)

/// Generates a query_naming clause for a viewdef.
let queryNaming ({ Name = n ; Params = ps } : DFunc) : Horn =
    QueryNaming { Name = n ; Params = List.map valueOf ps }

/// Constructs a full constraint in HSF.
/// The map of active globals should be passed as sharedVars.
/// Some is returned if the constraint is definite; None otherwise.
let hsfModelViewDef
  : (DFunc * VBoolExpr option) -> Result<Horn list, Error> =
    function
    | (vs, Some ex) ->
        lift2 (fun hd bd -> [Clause (hd, [bd]); Clause (bd, [hd])])
              (boolExpr makeHSFVar ex)
              (predOfFunc ensureArith vs)
        |> lift (fun c -> queryNaming vs :: c)
    | (vs, None) -> ok [ queryNaming vs ]

(*
 * Variables
 *)

/// Constructs a Horn clause for initialising an integer variable.
/// Returns an error if the variable is not an integer.
/// Returns no clause if the variable is not initialised.
/// Takes the environment of active global variables.
let hsfModelVariables (sharedVars : VarMap) : Result<Horn, Error> =
    let vpars =
        sharedVars
        |> Map.toSeq
        |> Seq.map
            (function
             | (name, Type.Int()) -> name |> makeHSFVar |> AVar |> ok
             | (name, ty) -> name |> withType ty |> NonArithVar |> fail)
        |> collect

    let head =
        bind
            (fun vp -> predOfFunc
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
let topLevelExpr : BoolExpr<MarkedVar> -> Result<Literal list, Error> =
    // The main difference here is that we model conjunctions directly as a
    // Horn literal list.
    function
    | BAnd xs -> xs
    | x -> [x]
    >> List.map (boolExpr unmarkVar)
    >> collect
    >> lift List.ofSeq

/// Generates an if-then-else, collapsing automatically in the case of true or false.
let ite (i : Literal) (t : Literal) (e : Literal) : Literal =
    match i with
    | True -> t
    | False -> e
    | _ -> ITE(i,t,e)

/// Constructs a Horn literal for a Func.
let hsfFunc
  (definer : FuncDefiner<BoolExpr<Var> option>)
  (func : MVFunc)
  : Result<Literal option, Error> =
    // We check the defining views here, because anything not in the
    // defining views is to be held true.
    // Now that we're at the func level, finding the view is easy!
    definer
    |> (FuncDefiner.lookup func >> mapMessages (curry InconsistentFunc func))
    |> bind (function
             | Some df -> lift Some (predOfFunc tryIntExpr func)
             | None -> ok None)

/// Constructs a Horn literal for a GFunc.
let hsfGFunc
  (definer : FuncDefiner<BoolExpr<Var> option>)
  ({ Cond = c; Item = ms } : GFunc<MarkedVar>)
  : Result<Literal option, Error> =
    hsfFunc definer ms
    |> (lift2 (fun cR -> Option.map (fun m -> ite cR m True))
              (boolExpr unmarkVar c))

/// Constructs the body for a set of condition pair Horn clauses,
/// given the defining views, preconditions and semantics clause.
let hsfConditionBody
  (definer : FuncDefiner<BoolExpr<Var> option>)
  (weakestPre : GView<MarkedVar>)
  (command : MBoolExpr)
  : Result<Literal list, Error> =
    let weakestPreH =
        weakestPre
        |> Multiset.toFlatSeq
        |> Seq.map (hsfGFunc definer)
        |> collect
        |> lift (Seq.choose id >> List.ofSeq)

    let commandH = topLevelExpr command

    lift2 List.append weakestPreH commandH

/// Constructs a series of Horn clauses for a term.
/// Takes the environment of active global variables.
let hsfTerm
  (definer : FuncDefiner<BoolExpr<Var> option>)
  (name : string,
   {Cmd = c; WPre = w ; Goal = g}
     : CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>)
  : Result<Horn list, Error> =
    lift2 (fun head body ->
           [ Comment (sprintf "term %s" name)
             Clause (Option.get head, body) ])
          (hsfFunc definer g)
          (hsfConditionBody definer w c.Semantics) // TODO: keep around Command?

/// Constructs a HSF script for a model.
let hsfModel
  ({ SharedVars = sharedVars; ViewDefs = definer; Axioms = xs }
     : Model<CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>,
             FuncDefiner<BoolExpr<Var> option>>)
  : Result<Horn list, Error> =
    let uniquify = Set.ofList >> Set.toList
    let collectMap f = Seq.map f >> collect

    trial {
        let! varHorn = hsfModelVariables sharedVars

        let! defHorns =
            definer
            |> FuncDefiner.toSeq
            |> collectMap hsfModelViewDef
            |> lift (List.concat >> uniquify)

        let! axHorns =
            xs
            |> Map.toSeq
            |> collectMap (hsfTerm definer)
            |> lift (List.concat >> uniquify)

        return varHorn :: List.append defHorns axHorns
    }
