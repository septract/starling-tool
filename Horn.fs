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
open Starling.Core.Traversal
open Starling.Core.Model
open Starling.Core.Symbolic
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
        /// A comment attached to a Horn clause.
        | Comment of cmt: string
        /// A query-naming call.
        | QueryNaming of Func<string>

    /// <summary>
    ///     An error caused when emitting a Horn clause.
    /// </summary>
    type Error =
        /// <summary>
        ///     A Func is inconsistent with its definition.
        /// </summary>
        | InconsistentFunc of func : MVFunc * err : Starling.Core.Definer.Error
        /// <summary>
        ///     A viewdef has a non-arithmetic param.
        /// </summary>
        | NonArithParam of TypedVar
        /// <summary>
        ///     A model has a non-arithmetic variable.
        /// </summary>
        | NonArithVar of TypedVar
        /// <summary>
        ///     The expression given is not supported in the given position.
        /// </summary>
        | UnsupportedExpr of VExpr
        /// <summary>
        ///     The expression given is compound, but empty.
        /// </summary>
        | EmptyCompoundExpr of exptype : string
        /// <summary>
        ///     HSF can't check the given deferred check.
        /// </summary>
        | CannotCheckDeferred of check : DeferredCheck * why : string
        /// <summary>
        ///     A traversal blew up somewhere.
        /// </summary>
        | Traversal of err : TraversalError<Error>


/// <summary>
///     Pretty printers for the Horn clause generator.
/// </summary>
/// Pretty-prints HSF translation errors.
module Pretty =
    open Starling.Core.Pretty
    open Starling.Collections.Func.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.View.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Traversal.Pretty

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
        | IVar c -> String c
        | IInt i -> sprintf "%d" i |> String
        | IIdx _ -> failwith "unexpected array index"
        // Do some reshuffling of n-ary expressions into binary ones.
        // These expressions are left-associative, so this should be sound.
        | IAdd [] -> failwith "unexpected empty addition"
        | IAdd [ x ] -> printInt x
        | IAdd [ x; y ] -> printBop "+" x y
        | IAdd(x :: y :: xs) -> printInt (IAdd((IAdd [ x; y ]) :: xs))
        | ISub [] -> failwith "unexpected empty subtraction"
        | ISub [ x ] -> printInt x
        | ISub [ x; y ] -> printBop "-" x y
        | ISub(x :: y :: xs) -> printInt (ISub((ISub [ x; y ]) :: xs))
        | IMul [] -> failwith "unexpected empty multiplication"
        | IMul [ x ] -> printInt x
        | IMul [ x; y ] -> printBop "*" x y
        | IMul(x :: y :: xs) -> printInt (IMul((IMul [ x; y ]) :: xs))
        | IDiv(x, y) -> printBop "/" x y
        | IMod(x, y) -> failwith "unexpected modulo"

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

    /// <summary>
    ///     Pretty-prints a HSF backend error.
    /// </summary>
    /// <param name="err">The error to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="err"/>.
    /// </returns>
    let rec printError (err : Error) : Doc =
        match err with
        | InconsistentFunc (func, err) ->
            wrapped "view func"
                    (printMVFunc func)
                    (Starling.Core.Definer.Pretty.printError err)
        | NonArithParam p ->
            error
                (String "invalid parameter '"
                 <-> printTypedVar p
                 <-> String "': HSF only permits integers here")
        | NonArithVar p ->
            error
                (String "invalid variable '"
                 <-> printTypedVar p
                 <-> String "': HSF only permits integers here")
        | UnsupportedExpr expr ->
            error
                (String "expression '"
                 <-> printVExpr expr
                 <-> String "' is not supported in the HSF backend")
        | EmptyCompoundExpr exptype ->
            error
                (String "found an empty '"
                 <-> String exptype
                 <-> String "' expression")
        | CannotCheckDeferred (check, why) ->
            error
                (String "deferred sanity check '"
                 <-> printDeferredCheck check
                 <-> String "' failed:"
                 <+> String why)
        | Traversal err -> printTraversalError printError err


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
        | IVar c -> c |> toVar |> IVar |> ok
        | IInt i -> i |> IInt |> ok
        | IAdd [] -> EmptyCompoundExpr "addition" |> fail
        | ISub [] -> EmptyCompoundExpr "subtraction" |> fail
        | IMul [] -> EmptyCompoundExpr "multiplication" |> fail
        | IAdd xs -> xs |> List.map ca |> collect |> lift IAdd
        | ISub xs -> xs |> List.map ca |> collect |> lift ISub
        | IMul xs -> xs |> List.map ca |> collect |> lift IMul
        | IDiv (x, y) -> lift2 (curry IDiv) (ca x) (ca y)
        | x ->
            (* Need to convert this expression into an Expr<Var> for the
               error message, which is somewhat painful and can itself fail! *)
            // TODO(CaptainHayashi): subtypes?
            let xExpr = Expr.Int (normalRec, x)
            let xVarExprR =
                liftWithoutContext
                    (toVar >> ok) (tliftOverCTyped >> tliftOverExpr)
                    xExpr
            bind
                (fun xVarExpr -> fail (UnsupportedExpr xVarExpr))
                (mapMessages Traversal xVarExprR)
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
    let tca = stripTypeRec >> ca

    let rec be =
        function
        // TODO(CaptainHayashi): are these allowed?
        | BAnd xs -> xs |> List.map be |> collect |> lift And
        | BOr xs -> xs |> List.map be |> collect |> lift Or
        | BTrue -> ok <| True
        | BFalse -> ok <| False
        // TODO(CaptainHayashi): should we be throwing away int subtypes?
        | BEq(Expr.Int (_, x), Expr.Int (_, y)) -> lift2 (curry Eq) (ca x) (ca y)
        | BNot(BEq(Expr.Int (_, x), Expr.Int (_, y))) -> lift2 (curry Neq) (ca x) (ca y)
        // TODO(CaptainHayashi): is implies allowed natively?
        | BImplies(x, y) -> be (mkOr [ mkNot x ; y ])
        | BGt(x, y) -> lift2 (curry Gt) (tca x) (tca y)
        | BGe(x, y) -> lift2 (curry Ge) (tca x) (tca y)
        | BLe(x, y) -> lift2 (curry Le) (tca x) (tca y)
        | BLt(x, y) -> lift2 (curry Lt) (tca x) (tca y)
        | x ->
            let everythingToVar =
                liftWithoutContext (toVar >> ok)
                    (tliftOverCTyped >> tliftOverExpr)
                >> mapMessages Traversal
            bind (UnsupportedExpr >> fail) (everythingToVar (Bool (normalRec, x)))
    be

(*
 * Func sanitisation
 *)

/// <summary>
///     Tries to convert a marked expression into an unmarked integer
///     expression by mangling the marks into unique names.
/// </summary>
/// <param name="expr">The expression to convert.</param>
/// <returns>
///     If successful, the resulting integer expression.
///     Fails with <see cref="UnsupportedExpr"/> if the expression is
///     Boolean.
/// </returns>
let tryIntExpr (expr : Expr<MarkedVar>) : Result<IntExpr<Var>, Error> =
    let mapper =
        liftWithoutContext (unmarkVar >> ok)
            (tliftOverCTyped >> tliftOverExpr)

    let filterExpr =
        // TODO(CaptainHayashi): subtypes?
        function
        | Expr.Int (_, x) -> ok x
        | e -> fail (UnsupportedExpr e)

    bind filterExpr (mapMessages Traversal (mapper expr))

///<summary>
///     HSF requires variables to start with a capital letter.
///     so we prepend a "V".  This is also done in unmarkVar.
///     @mjp41: TODO: We should consider consolidating this.
///</summary>
let makeHSFVar : string -> string = (+) "V"

/// Ensures a param in a viewdef multiset is arithmetic.
let ensureArith : TypedVar -> Result<IntExpr<Var>, Error> =
    // TODO(CaptainHayashi): subtypes?
    function
    | Int (_, x) -> x |> makeHSFVar |> IVar |> ok
    | x -> x |> NonArithParam |> fail

/// Constructs a pred from a Func, given a set of active globals,
/// and some validator on the parameters.
let predOfFunc
  (parT : 'par -> Result<VIntExpr, Error>)
  ({ Name = n; Params = pars } : Func<'par>)
  : Result<Func<VIntExpr>, Error> =
    lift (fun parR -> { Name = n; Params = parR })
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
        lift2 (fun hd bdp ->
                let bd = Pred bdp
                [Clause (hd, [bd]); Clause (bd, [hd])])
              (boolExpr makeHSFVar ex)
              (predOfFunc ensureArith vs)
        |> lift (fun c -> queryNaming vs :: c)
    | (vs, None) -> ok [ queryNaming vs ]

(*
 * Variables
 *)

/// <summary>
///     Generates the Horn uninterpreted function for emp.
/// </summary>
/// <param name="svars">The shared vars used as parameters to emp.</param>
/// <returns>
///     If successful, the Horn uninterpreted function for emp.
/// </returns>
let predOfEmp (svars : VarMap) : Result<Func<VIntExpr>, Error> =
    let svarSeq = VarMap.toTypedVarSeq svars

    (* emp is parameterised by the entire shared state, but nothing else.
       We can't make the predicate if any of those variables are non-integer. *)
    let empParamsR =
        collect
            (Seq.map
                // TODO(CaptainHayashi): subtypes?
                (function
                 | Int (_, name) -> ok (IVar (makeHSFVar name))
                 | var -> fail (NonArithVar var))
                svarSeq)

    bind (fun empParams -> predOfFunc ok { Name = "emp"; Params = empParams })
        empParamsR

/// Constructs a Horn clause for initialising an integer variable.
/// Returns an error if the variable is not an integer.
/// Returns no clause if the variable is not initialised.
/// Takes the environment of active global variables.
let hsfModelVariables (svars : VarMap) : Result<Horn, Error> =
    // TODO(CaptainHayashi): actually get these initialisations from
    // somewhere instead of assuming everything to be 0L.
    lift
        (fun hd ->
            let vps = hd.Params
            Clause(Pred hd, List.map (fun n -> Eq (n, IInt 0L)) vps ))
        (predOfEmp svars)

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
             | Some df -> lift (Pred >> Some) (predOfFunc tryIntExpr func)
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

/// <summary>
///     Given the name of an iterator, map a function over the parameter in a
///     func that represents that iterator.
/// </summary>
/// <param name="iterator">The name of the iterator to transform.<param>
/// <param name="f">The function mapping the iterator to an expression.</param>
/// <param name="func">
///     The func in which <paramref name="iterator"/> is a parameter.
/// </param>
/// <returns>
///     <paramref name="func"/>, with the iterator transformed by
///     <paramref name="f"/>.
/// </returns>
let mapIteratorParam
  (iterator : Var) (f : Var -> IntExpr<Var>) (func : Func<IntExpr<Var>>)
  : Func<IntExpr<Var>> =
    (* We don't check that the iterator is only in there once, and instead just
       map over each ocurrence.  This should be sound by construction. *)

    let fOnIter param =
        match param with
        | IVar var when var = iterator -> f var
        | x -> x
    { func with Params = List.map fOnIter func.Params }

/// <summary>
///     Constructs a Horn clause for a base downclosure check on a given func.
/// </summary>
let hsfModelBaseDownclosure
  (svars : VarMap) (func : IteratedDFunc)
  (defn : BoolExpr<Sym<Var>> option)
  (reason : string)
  : Result<Horn list, Error> =
    // TODO(CaptainHayashi): proper doc comment.
    let svarSeq = VarMap.toTypedVarSeq svars

    (* TODO(CaptainHayashi): We're given the func needing downclosure in
       unflattened form.  This is kind-of messy, as we now have to flatten
       it again. *)
    let flatFunc = Starling.Flattener.flattenDView svarSeq [func]
    let funcPredR = predOfFunc ensureArith flatFunc

    // TODO(CaptainHayashi): lots of duplication here.
    let iterator = func.Iterator
    let iterVarR =
        // TODO(CaptainHayashi): subtypes?
        match iterator with
        | Some (Int (_, x)) -> ok x
        | _ ->
            fail
                (CannotCheckDeferred
                    (NeedsBaseDownclosure (func, defn, reason), "malformed iterator"))

    (* Base downclosure for a view V[n](x):
         D(emp) => D(V[0](x))
       That is, the definition of V when the iterator is 0 can be no
       stricter than the definition of emp.

       In the following, `funcPredZeroR` models V[0](x) by transforming
       the iterator from n to 0 in `funcPredR`, and 'empPredR' models emp. *)
    let funcPredZeroR =
        lift2
            (fun it pred -> mapIteratorParam it (fun _ -> IInt 0L) pred)
            iterVarR
            funcPredR
    let empPredR = predOfEmp svars

    // The above can be modelled as the Horn clause funcPredZero :- empPred.
    let hornR =
        lift2
            (fun funcPredZero empPred ->
                Clause (Pred funcPredZero, [Pred empPred]))
            funcPredZeroR
            empPredR

    // We then add a comment to help show where this came from.
    lift
        (fun h ->
            [ Comment
                (sprintf "base downclosure on %s: %s" func.Func.Name reason)
              h ])
        hornR

/// <summary>
///     Constructs a Horn clause for an inductive downclosure check on a given
///     func.
/// </summary>
let hsfModelInductiveDownclosure
  (svars : VarMap) (func : IteratedDFunc) (defn : BoolExpr<Sym<Var>> option) (reason : string)
  : Result<Horn list, Error> =
    // TODO(CaptainHayashi): proper doc comment.
    let svarSeq = VarMap.toTypedVarSeq svars

    // See hsfModelBaseDownclosure for caveats.
    let flatFunc = Starling.Flattener.flattenDView svarSeq [func]
    let funcPredR = predOfFunc ensureArith flatFunc

    let iterator = func.Iterator
    let iterVarR =
        // TODO(CaptainHayashi): subtypes?
        match iterator with
        | Some (Int (_, x)) -> ok x
        | _ ->
            fail
                (CannotCheckDeferred
                    (NeedsInductiveDownclosure (func, defn, reason),
                     "malformed iterator"))

    (* Inductive downclosure for a view V[n](x):
         (0 <= n) => (D(V[n+1](x)) => D(V[n](x)))
       That is, the definition of V when the iterator is n+1 implies the
       definition of V when the iterator is n, for all positive n.

       In the following, `funcPredSuccR` models V[n+1](x) by transforming
       the iterator from n to n+1 in `funcPredR`. *)
    let funcPredSuccR =
        lift2
            (fun it pred -> mapIteratorParam it incVar pred)
            iterVarR
            funcPredR

    (* The above can be modelled as the Horn clause
         funcPredR :- n > 0, funcPredSuccR.
       (We flatten the nested implication into a conjunction.) *)
    let hornR =
        lift3
            (fun it succ norm ->
                Clause (Pred norm, [Ge (IVar it, IInt 0L); Pred succ]))
            iterVarR
            funcPredSuccR
            funcPredR

    // As with base DC, comment to show where this clause originated.
    lift
        (fun h ->
            [ Comment (sprintf "ind downclosure on %s: %s" func.Func.Name reason)
              h ])
        hornR

/// <summary>
///     Constructs a Horn clause for a deferred check, if possible.
/// </summary>
let hsfModelDeferredCheck (svars : VarMap) (check : DeferredCheck)
  : Result<Horn list, Error> =
    match check with
    | NeedsBaseDownclosure (func, defn, reason) ->
        hsfModelBaseDownclosure svars func defn reason
    | NeedsInductiveDownclosure (func, defn, reason) ->
        hsfModelInductiveDownclosure svars func defn reason

/// Constructs a HSF script for a model.
let hsfModel
  ({ SharedVars = svars; ViewDefs = definer; Axioms = xs; DeferredChecks = ds }
     : Model<CmdTerm<MBoolExpr, GView<MarkedVar>, MVFunc>,
             FuncDefiner<BoolExpr<Var> option>>)
  : Result<Horn list, Error> =
    // This is complicated so as to preserve order.
    let uniquify hs =
        let f seenSoFar horn =
            match horn with
            | Clause (_) as c ->
                if (Set.contains c seenSoFar)
                then (seenSoFar, Comment "(duplicate clause)")
                else (Set.add c seenSoFar, c)
            | l -> (seenSoFar, l)
        snd (mapAccumL f Set.empty hs)

    let collectMap f = Seq.map f >> collect

    trial {
        let! varHorn = hsfModelVariables svars

        let! dcHorns =
            lift
                (List.concat >> uniquify)
                (collectMap (hsfModelDeferredCheck svars) ds)

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

        return varHorn :: List.concat [ defHorns; axHorns; dcHorns ]
    }
