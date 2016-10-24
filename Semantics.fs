/// <summary>
///   Module containing the semantic instantiator.
///
///   <para>
///     The semantic instantiator converts the commands in a model's
///     axioms into Boolean expressions, by instantiating them in
///     accordance with the model's semantic definitions.
///   </para>
///   <para>
///     It also ensures variables not mentioned in a command's semantic
///     definition are preserved in the resulting expression.
///   </para>
/// </summary>
module Starling.Semantics

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Core.TypeSystem
open Starling.Core.TypeSystem.Check
open Starling.Core.Command
open Starling.Core.Command.Compose
open Starling.Core.GuardedView
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.Traversal


/// <summary>
///     Types used in the Semantics stage.
/// </summary>
[<AutoOpen>]
module Types =
    /// Type of errors relating to semantics instantiation.
    type Error =
        /// There was an error instantiating a semantic definition.
        | Instantiate of prim: PrimCommand
                       * error: Error
        /// A primitive has a missing semantic definition.
        | MissingDef of prim: PrimCommand
        /// Got unexpected number of arguments
        | CountMismatch of expected: int * actual: int
        | TypeMismatch of param: TypedVar * atype: Type
        /// <summary>
        ///     We tried to substitute parameters, but one parameter was free
        ///     (not bound to an expression) somehow.
        /// </summary>
        | FreeVarInSub of param: TypedVar
        /// <summary>
        ///     An error occurred during traversal.
        ///     This error may contain nested semantics errors!
        /// </summary>
        | Traversal of TraversalError<Error>


/// <summary>
///     Pretty printers used in the Semantics stage.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.Model.Pretty

    /// Pretty-prints semantics errors.
    let rec printSemanticsError =
        function
        | Instantiate (prim, error) ->
          colonSep
              [ fmt "couldn't instantiate primitive '{0}'"
                    [ printPrimCommand prim ]
                printSemanticsError error ]
        | MissingDef prim ->
            fmt "primitive '{0}' has no semantic definition"
                [ printPrimCommand prim ]
        | TypeMismatch (par, atype) ->
            fmt "parameter '{0}' conflicts with argument of type '{1}'"
                [ printTypedVar par; printType atype ]
        | CountMismatch (fn, dn) ->
            fmt "view usage has {0} parameter(s), but its definition has {1}"
                [ fn |> sprintf "%d" |> String; dn |> sprintf "%d" |> String ]
        | FreeVarInSub var ->
            // TODO(CaptainHayashi): this is a bit shoddy.
            error
                (hsep
                    [ String "parameter '"
                      printTypedVar var
                      String "' has no substitution" ])
        | Traversal err ->
            Starling.Core.Traversal.Pretty.printTraversalError printSemanticsError err

/// Generates a framing relation for a given variable.
let frameVar ctor (par : CTyped<Var>) : SMBoolExpr =
    BEq (par |> mapCTyped (After >> Reg) |> mkVarExp,
         par |> mapCTyped (ctor >> Reg) |> mkVarExp)

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame svars tvars expr =
    (* First, we need to find all the bound post-variables in the expression.
       We do this by finding _all_ variables, then filtering. *)
    let varsInExprResult =
        findMarkedVars
            (tLiftToBoolSrc (tliftToExprDest collectSymMarkedVars))
            expr
    let untypedVarsInExprResult = lift (Seq.map valueOf) varsInExprResult

    let aftersInExprResult =
        lift (Seq.choose (function After x -> Some x | _ -> None))
            untypedVarsInExprResult

    let evarsResult = lift Set.ofSeq aftersInExprResult


    (* Then, for all of the variables in the model, choose those not in evars,
       and make frame expressions for them. *)
    let allVars = Seq.append (Map.toSeq svars) (Map.toSeq tvars)

    let makeFrames evars =
    // TODO(CaptainHayashi): this is fairly inefficient.
        let varsNotInEvars =
            Seq.filter (fun (name, _) -> not (Set.contains name evars)) allVars

        let markedVarsNotInEvars =
            Seq.map
                (fun (name, ty) ->
                    let next = getBoolIntermediate name expr
                    match next with
                    | None   -> (name, ty, Before)
                    | Some i -> (name, ty, (fun x -> (Intermediate(i, x)))))
                varsNotInEvars

        Seq.map (fun (name, ty, ctor) -> frameVar ctor (withType ty name))
            markedVarsNotInEvars

    lift makeFrames evarsResult

let primParamSubFun
  ( cmd : PrimCommand )
  ( sem : PrimSemantics )
  : Traversal<TypedVar, Expr<Sym<MarkedVar>>, Error> =
    /// merge the pre + post conditions
    let paramToMExpr : Traversal<Expr<Sym<Var>>, Expr<Sym<MarkedVar>>, Error> =
        tliftOverExpr (traverseTypedSymWithMarker After)

    let fparsResult =
        mapTraversal
            (tchainL paramToMExpr (List.append cmd.Args))
            cmd.Results

    let dpars = sem.Args @ sem.Results

    let pmapResult =
        lift
            (Map.ofSeq << Seq.map2 (fun par up -> valueOf par, up) dpars)
            fparsResult

    let travFromMap (pmap : Map<Var, Expr<Sym<MarkedVar>>>) =
        ignoreContext
            (function
             | WithType (var, vtype) as v ->
                match pmap.TryFind var with
                | Some tvar ->
                    if vtype = typeOf tvar
                    then ok tvar
                    else fail (Inner (TypeMismatch (v, typeOf tvar)))
                | None -> fail (Inner (FreeVarInSub v)))
    fun ctx e -> bind (fun pmap -> travFromMap pmap ctx e) pmapResult

let checkParamCountPrim : PrimCommand -> PrimSemantics option -> Result<PrimSemantics option, Error> =
    fun prim opt ->
    match opt with
    | None -> ok None
    | Some def ->
        let fn = List.length prim.Args
        let dn = List.length def.Args
        if fn = dn then ok (Some def) else CountMismatch (fn, dn) |> fail

let lookupPrim : PrimCommand -> PrimSemanticsMap -> Result<PrimSemantics option, Error>  =
    fun prim map ->
    checkParamCountPrim prim
    <| Map.tryFind prim.Name map

let checkParamTypesPrim : PrimCommand -> PrimSemantics -> Result<PrimCommand, Error> =
    fun prim sem ->
    List.map2
        (curry
             (function
              | UnifyInt _ | UnifyBool _ -> ok ()
              | UnifyFail (fp, dp) -> fail (TypeMismatch (dp, typeOf fp))))
        prim.Args
        sem.Args
    |> collect
    |> lift (fun _ -> prim)



/// Instantiates a PrimCommand from a PrimSemantics instance
let instantiatePrim
  (smap : PrimSemanticsMap)
  (prim : PrimCommand)
  : Result<SMBoolExpr option, Error> =
    let primDefResult = lookupPrim prim smap
    let typeCheckedDefResult =
        bind
            (function
             | None -> ok None
             | Some sem ->
                lift (fun _ -> Some sem) (checkParamTypesPrim prim sem))
            primDefResult

    let instantiate =
        function
        | None -> ok None
        | Some s ->
            let subInTypedSym =
                    tliftToTypedSymVarSrc (primParamSubFun prim s)
            let subInBool = tLiftToBoolSrc subInTypedSym
            let subbed = lift Some (mapTraversal subInBool s.Body)
            mapMessages Traversal subbed

    bind instantiate typeCheckedDefResult

/// Translate a primitive command to an expression characterising it
/// by instantiating the semantics from the core semantics map with
/// the variables from the command
let instantiateSemanticsOfPrim
  (semantics : PrimSemanticsMap)
  (prim : PrimCommand)
  : Result<SMBoolExpr, Error> =
    (* First, instantiate according to the semantics.
     * This can succeed but return None.  This means there is no
     * entry (erroneous or otherwise) in the semantics for this prim.
     * Since this is an error in this case, make it one.
     *)
    prim
    |> wrapMessages Instantiate (instantiatePrim semantics)  // TODO: Remove this line? maybe not needed anymore.
    |> bind (failIfNone (MissingDef prim))

/// Given a list of BoolExpr's it sequentially composes them together
/// this works by taking each BoolExpr in turn,
///     converting *all* After variables to (Intermediate i) variables
///     converts any Before variables where an Intermediate exists, to that Intermediate
///
/// the frame can then be constructed by taking the BoolExpr and looking for the aforementioned Intermediate
/// variables and adding a (= (After v) (Intermediate maxInterValue v)) if it finds one
let seqComposition (xs : BoolExpr<Sym<MarkedVar>> list)
  : Result<BoolExpr<Sym<MarkedVar>>, Error> =
    // since we are trying to keep track of explicit state (where we are in terms of the intermediate variables)
    // it's _okay_ to include actual mutable state here!
    let mutable dict = System.Collections.Generic.Dictionary<Var, bigint>()

    let mapper x =
        let dict2 = System.Collections.Generic.Dictionary<Var, bigint>(dict)
        let isSet = System.Collections.Generic.HashSet<Var>()

        let xRewriteVar =
            function
            | Before v as v' ->
                if dict.ContainsKey (v) then
                    let iv = dict.[v]
                    Reg (Intermediate(iv, v))
                else
                    Reg v'
            | After v ->
                /// Have not set After v to a new Intermediate yet
                if not (isSet.Contains(v)) then
                    ignore <| isSet.Add(v)

                    if dict2.ContainsKey(v) then
                        let nLevel = dict2.[v] + 1I
                        ignore <| dict2.Remove(v)
                        dict2.Add(v, nLevel)
                        Reg (Intermediate (nLevel, v))
                    else
                        dict2.Add(v, 0I)
                        Reg (Intermediate (0I, v))
                else
                    Reg (Intermediate (dict2.[v], v))
            | v -> Reg v

        let xRewriteBool =
            tLiftToBoolSrc
                (tliftToExprDest
                    (tliftOverCTyped
                        (tliftToSymSrc
                            (ignoreContext (xRewriteVar >> ok)))))

        let bexprResult = mapTraversal xRewriteBool x
        dict <- dict2
        bexprResult

    let rec mapping =
        function
        | []        ->  ok BTrue
        | x :: ys   ->  lift2 mkAnd2 (mapper x) (mapping ys)

    mapMessages Traversal (mapping xs)

/// Given a BoolExpr add the frame and return the new BoolExpr
let addFrame svars tvars bexpr =
    let frameSeqResult = frame svars tvars bexpr
    let frameResult = lift (List.ofSeq >> mkAnd) frameSeqResult
    let addResult = lift (flip mkAnd2 bexpr) frameResult
    mapMessages Traversal addResult

/// Translate a command to an expression characterising it.
/// This is the sequential composition of the translations of each
/// primitive inside it.
let semanticsOfCommand
  (semantics : PrimSemanticsMap)
  (svars : VarMap)
  (tvars : VarMap)
  (cmd : Command) : Result<CommandSemantics<SMBoolExpr>, Error> =
    // Instantiate the semantic function of each primitive
    Seq.map (instantiateSemanticsOfPrim semantics) cmd
    |> collect

    // Compose them together with intermediates
    |> bind seqComposition

    // Add the frame
    |> bind (addFrame svars tvars)
    |> lift (fun bexpr -> { Cmd = cmd; Semantics = bexpr })

open Starling.Core.Axiom.Types
/// Translate a model over Prims to a model over semantic expressions.
let translate
  (model : Model<GoalAxiom<Command>, 'viewdef>)
  : Result<Model<GoalAxiom<CommandSemantics<SMBoolExpr>>, 'viewdef>, Error> =
    let modelSemantics = semanticsOfCommand model.Semantics model.SharedVars model.ThreadVars
    let replaceCmd ga c = { Goal = ga.Goal; Axiom = {Pre = ga.Axiom.Pre; Post = ga.Axiom.Post; Cmd = c }}
    let transSem ga = bind (replaceCmd ga >> ok) (modelSemantics ga.Axiom.Cmd)
    tryMapAxioms transSem model
