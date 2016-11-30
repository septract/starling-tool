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
open Starling.Core.Command
open Starling.Core.Command.Compose
open Starling.Core.GuardedView
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
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
        ///     The semantics of a command is ill-formed.
        /// </summary>
        | BadSemantics of why : string
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
        | BadSemantics why ->
            errorStr "internal semantics error:" <+> errorStr why
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

/// <summary>
///     A write record for an variable.
///
///     <para>
///         Write records are used to build frames, by calculating which bits
///         of an variable have been modified by a command.
/// </summary>
type Write =
    /// <summary>The entire lvalue has been written to.</summary>
    | Entire of newVal : Expr<Sym<Var>>
    /// <summary>
    ///     Only certain parts of the lvalue have been written to,
    ///     and their recursive write records are enclosed.
    /// </summary>
    | Indices of Map<IntExpr<Sym<Var>>, Write>
    override this.ToString () = sprintf "%A" this

/// <summary>
///     Records a write into a write map.
/// </summary>
/// <param name="var">The variable being written to.</param>
/// <param name="idxPath">
///     The path of indexes from the variable being written to to the variable.
///     For example, [3; x; 1+i] would represent a write to A[3][x][1+i].
/// </param>
/// <param name="value">The value written to the eventual destination.</param>
/// <param name="map">The write map being extended.</param>
/// <returns>The extended write map.</returns>
let markWrite (var : TypedVar) (idxPath : IntExpr<Sym<Var>> list)
  (value : Expr<Sym<Var>>)
  (map : Map<TypedVar, Write>)
  : Map<TypedVar, Write> =
    (* First, consider what it means to add an index write to an index write
       map. *)
    let rec markWriteIdx
      (idx : IntExpr<Sym<Var>>)
      (idxPathRest : IntExpr<Sym<Var>> list)
      (imap : Map<IntExpr<Sym<Var>>, Write>) =
        // Find out if we've already written to this index.
        let idxRec = imap.TryFind idx
        let imapLessIdx =
            maybe imap (fun _ -> imap.Remove idx) (imap.TryFind idx)

        let idxRec' =
            match idxPathRest with
            | [] ->
                (* If there is no subscript, then we must be writing to this
                   entire index, so mark it as Entire... if it isn't already
                   written to. *)
                match idxRec with
                | Some _ -> failwith "markWriteIdx: tried to write twice with empty path"
                | None -> Entire value
            | x::xs ->
                match idxRec with
                | Some (Entire _) -> failwith "markWriteIdx: tried to write twice with nonempty path"
                | Some (Indices imap) -> markWriteIdx x xs imap
                | None -> markWriteIdx x xs Map.empty

        Indices (Map.add idx idxRec' imapLessIdx)


    // Now we can define the top-level.

    let varRec = map.TryFind var
    let mapLessVar = maybe map (fun _ -> map.Remove var) (map.TryFind var)

    let varRec' =
        match idxPath with
        | [] ->
            (* If there is no subscript, then we must be writing to this entire
               variable, so mark it as Entire... if it isn't already written to. *)
            match varRec with
            | Some _ -> failwith "markWrite: tried to write twice with empty path"
            | None -> Entire value
        | (x::xs) ->
            match varRec with
            | Some (Entire _) -> failwith "markWrite: tried to write twice with nonempty path"
            | Some (Indices imap) -> markWriteIdx x xs imap
            | None -> markWriteIdx x xs Map.empty

    Map.add var varRec' mapLessVar

/// <summary>
///     Tries to extract the variable and index path from a lvalue.
/// </summary>
let varAndIdxPath (expr : Expr<Sym<Var>>)
  : (TypedVar * IntExpr<Sym<Var>> list) option =
    // TODO(CaptainHayashi): proper doc comment.
    // TODO(CaptainHayashi): merge with type lookup stuff in Modeller?
    // TODO(CaptainHayashi): error perhaps if given a non-lvalue

    let rec getInBool bx path =
        match bx with
        | BVar (Reg v) -> Some (Bool v, path)
        // Symbols are not lvalues, so we can't process them.
        | BIdx (e, l, a, i) -> getInArray e l a (i::path)
        | _ -> None
    and getInInt ix path =
        match ix with
        | IVar (Reg v) -> Some (Int v, path)
        // Symbols are not lvalues, so we can't process them.
        | IIdx (e, l, a, i) -> getInArray e l a (i::path)
        | _ -> None
    and getInArray eltype length ax path =
        match ax with
        | AVar (Reg v) -> Some (Array (eltype, length, v), path)
        // Symbols are not lvalues, so we can't process them.
        | AIdx (e, l, a, i) -> getInArray e l a (i::path)
        | _ -> None

    match expr with
    | Int ix -> getInInt ix []
    | Bool bx -> getInBool bx []
    | Array (eltype, length, ax) -> getInArray eltype length ax []

/// <summary>
///     Generates a write record map for a given assignment list.
/// </summary>
/// <param name="assigns">The assignment list to investigate.</param>
/// <returns>The write map for that microcode list.</returns>
let makeWriteMap (assigns : (Expr<Sym<Var>> * Expr<Sym<Var>>) list)
  : Map<TypedVar, Write> =
    let addToWriteMap map (lv, rv) =
        // TODO(CaptainHayashi): complain if lv isn't a lvalue?
        maybe map (fun (var, idx) -> markWrite var idx rv map) (varAndIdxPath lv)
    List.fold addToWriteMap Map.empty assigns

/// <summary>
///     Partitions a list of microcode instructions.
/// </summary>
/// <param name="instrs">The instructions to partition.</param>
/// <returns>
///     A triple containing a list of assignments, a list of assumptions,
///     and a list of (unpartitioned) microcode branches.
/// </returns>
let partitionMicrocode (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>> list)
  : ((Expr<Sym<Var>> * Expr<Sym<Var>>) list
     * BoolExpr<Sym<Var>> list
     * (BoolExpr<Sym<Var>>
        * Microcode<Expr<Sym<Var>>, Sym<Var>> list
        * Microcode<Expr<Sym<Var>>, Sym<Var>> list) list) =
    let partitionStep (assigns, assumes, branches) instr =
        match instr with
        | Assign (l, r) -> ((l, r)::assigns, assumes, branches)
        | Assume s -> (assigns, s::assumes, branches)
        | Branch (i, t, e) -> (assigns, assumes, (i, t, e)::branches)
    List.fold partitionStep ([], [], []) instrs

/// <summary>
///     Generates a well-typed expression for a subscript of a given array.
/// </summary>
/// <param name="eltype">The type of elements in the array.</param>
/// <param name="length">The length of the array.</param>
/// <param name="array">The array to subscript.</param>
/// <param name="idx">The index to subscript by.</param>
/// <returns>A well-typed <see cref="Expr"/> capturing the subscript.</returns>
let mkIdx (eltype : Type) (length : int option) (arr : ArrayExpr<Sym<Var>>)
  (idx : IntExpr<Sym<Var>>)
  : Expr<Sym<Var>> =
    let record = (eltype, length, arr, idx)

    match eltype with
    | Type.Int () -> Expr.Int (IIdx record)
    | Type.Bool () -> Expr.Bool (BIdx record)
    | Type.Array (eltype', length', ()) -> Expr.Array (eltype', length', AIdx record)

/// <summary>
///     Normalises a list of assignments such that they represent
///     entire-variable assignments.
///     <para>
///         This converts array-subscript assignments into assignments of
///         arrays to array updates.
///         This allows the framing logic to frame on a per-variable basis
///         in the presence of arrays.
///     </para>
/// </summary>
/// <param name="assigns">The assignments to normalise.</param>
/// <returns>
///     The assignments in entire-variable form, in arbitrary order.
/// </returns>
let normaliseAssigns (assigns : (Expr<Sym<Var>> * Expr<Sym<Var>>) list)
  : Result<(TypedVar * Expr<Sym<Var>>) list, Error> =
    // First, we convert the assigns to a write map.
    let wmap = makeWriteMap assigns
    (* Then, each item in the write map represents an assignment.
       We need to convert each write map entry into an array update or a
       direct value. *)
    let rec translateRhs lhs =
        function
        | Entire v -> ok v
        | Indices ixmap ->
            // TODO(CaptainHayashi): proper errors.
            match lhs with
            | Array (eltype, length, alhs) ->
                let addUpdate
                  (index : IntExpr<Sym<Var>>, value : Write) (lhs' : Expr<Sym<Var>>)
                  : Result<Expr<Sym<Var>>, Error> =
                    (* Need to translate any further subscripts inside value.
                       But, to do that, we need to know what the LHS of those
                       subscripts is! *)
                    let vlhs = mkIdx eltype length alhs index
                    let vrhsResult = translateRhs vlhs value
                    lift
                        (fun vrhs ->
                            Expr.Array
                                (eltype, length,
                                 AUpd (eltype, length, alhs, index, vrhs)))
                        vrhsResult
                seqBind addUpdate lhs (Map.toSeq ixmap)
            | _ -> fail (BadSemantics "tried to index into a non-array")

    let translateAssign (lhs : TypedVar, rhs) =
        // lhs is a typed variable here, but must be an expression for the above
        let lhsE = mkVarExp (mapCTyped Reg lhs)
        lift (mkPair lhs) (translateRhs lhsE rhs)

    collect (Seq.map translateAssign (Map.toSeq wmap))

/// <summary>
///     Normalises a microcode listing.
/// </summary>
/// <param name="instrs">The set of instructions to normalise.</param>
/// <returns>On success, the normalised listing (in arbitrary order).</returns>
let rec normaliseMicrocode
  (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>> list)
  : Result<Microcode<TypedVar, Sym<Var>> list, Error> =
    let assigns, assumes, branches = partitionMicrocode instrs

    let normaliseBranch (i, t, e) =
        let t'Result = normaliseMicrocode t
        let e'Result = normaliseMicrocode e
        lift2 (fun t' e' -> (i, t', e')) t'Result e'Result

    let branches'Result = collect (Seq.map normaliseBranch branches)
    let assigns'Result = normaliseAssigns assigns

    lift2
        (fun branches' assigns' ->
            List.concat
                [ List.map Assign assigns'
                  List.map Assume assumes
                  List.map Branch branches' ])
        branches'Result
        assigns'Result

/// Generates a frame for a given expression.
/// The frame is a relation a!after = a!before for every a not mentioned in the expression.
let frame svars tvars expr =
    (* First, we need to find all the bound post-variables in the expression.
       We do this by finding _all_ variables, then filtering. *)
    let varsInExprResult =
        findVars
            (tliftToBoolSrc (tliftToExprDest collectSymVars))
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
  (cmd : PrimCommand)
  (sem : PrimSemantics)
  : Traversal<TypedVar, Expr<Sym<Var>>, Error, unit> =

    let fpars = List.append cmd.Args cmd.Results
    let dpars = sem.Args @ sem.Results

    let pmap =
        Map.ofSeq (Seq.map2 (fun par up -> valueOf par, up) dpars fpars)

    ignoreContext
        (function
         | WithType (var, vtype) as v ->
            match pmap.TryFind var with
            | Some tvar ->
                if vtype = typeOf tvar
                then ok tvar
                else fail (Inner (TypeMismatch (v, typeOf tvar)))
            | None -> fail (Inner (FreeVarInSub v)))

let checkParamCountPrim (prim : PrimCommand) (opt : PrimSemantics option) : Result<PrimSemantics option, Error> =
    match opt with
    | None -> ok None
    | Some def ->
        let fn = List.length prim.Args
        let dn = List.length def.Args
        if fn = dn then ok (Some def) else CountMismatch (fn, dn) |> fail

let lookupPrim (prim : PrimCommand) (map : PrimSemanticsMap) : Result<PrimSemantics option, Error>  =
    checkParamCountPrim prim
    <| Map.tryFind prim.Name map

let checkParamTypesPrim (prim : PrimCommand) (sem : PrimSemantics) : Result<PrimCommand, Error> =
    List.map2
        (fun fp dp ->
            if typesCompatible (typeOf fp) (typeOf dp)
            then ok ()
            else fail (TypeMismatch (dp, typeOf fp)))
        prim.Args
        sem.Args
    |> collect
    |> lift (fun _ -> prim)

/// <summary>
///     Lifts a parameter instantiation traversal onto a microcode instruction.
/// </summary>
/// <param name="trav">The traversal to lift onto microcode.</param>
/// <typeparam name="Var">The type of context variables.</typeparam>
/// <returns>
///     A traversal that visits all of the lvalues and rvalues in a microcode
///     instruction.
/// </returns>
let tliftToMicrocode
  (trav : Traversal<TypedVar, Expr<Sym<Var>>, Error, 'Var>)
  : Traversal<Microcode<TypedVar, Var>,
              Microcode<Expr<Sym<Var>>, Sym<Var>>, Error, 'Var> =
    let travE : Traversal<Expr<Var>, Expr<Sym<Var>>, Error, 'Var> =
        tliftToExprSrc trav
    let travB : Traversal<BoolExpr<Var>, BoolExpr<Sym<Var>>, Error, 'Var> =
        tliftToBoolSrc trav

    let rec tm ctx mc =
        let tml = tchainL tm id

        match mc with
        | Assign (lv, rv) -> tchain2 trav travE Assign ctx (lv, rv)
        | Assume assumption -> tchain travB Assume ctx assumption
        | Branch (i, t, e) -> tchain3 travB tml tml Branch ctx (i, t, e)
    tm

/// <summary>
///     Converts a microcode instruction set into a two-state Boolean predicate.
/// </summary>
let microcodeToBool
  (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>> list)
  : Result<BoolExpr<Sym<MarkedVar>>, Error> =
    (* First, normalise the expression: this will make framing much easier
       later. *)
    let normalisedResult = normaliseMicrocode instrs

    (* We need some traversals to rewrite the expressions to their
       pre- and post-states.  The normalisation has already sifted things that
       are post-states onto the LHS of an Assign, and pre-states everywhere
       else. *)
    let toAfter = traverseTypedSymWithMarker After
    let toAfterV =
        mapTraversal (tliftToExprDest toAfter)
        >> mapMessages Traversal
    let toBefore = traverseTypedSymWithMarker Before
    let toBeforeE =
        mapTraversal (tliftOverExpr toBefore) >> mapMessages Traversal
    let toBeforeB =
        mapTraversal (tliftToBoolSrc (tliftToExprDest toBefore))
        >> mapMessages Traversal

    let rec translateInstrs is =
        // TODO(CaptainHayashi): convert to variable LVs.
        // TODO(CaptainHayashi): framing (currently done elsewhere).
        let translateInstr =
            function
            | Assign (x, y) -> lift2 mkEq (toAfterV (mapCTyped Reg x)) (toBeforeE y)
            | Assume x -> toBeforeB x
            | Branch (i, t, e) ->
                lift3
                    (fun iX tX eX ->
                        mkAnd2 (mkImplies iX tX) (mkImplies (mkNot iX) eX))
                    (toBeforeB i)
                    (translateInstrs t)
                    (translateInstrs e)
        lift mkAnd (collect (List.map translateInstr is))

    bind translateInstrs normalisedResult

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
            let subInMCode =
                    tchainL (tliftToMicrocode (primParamSubFun prim s)) id
            let subbedMCode =
                mapMessages Traversal (mapTraversal subInMCode s.Body)
            let subbed = bind microcodeToBool subbedMCode
            lift Some subbed

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
    |> wrapMessages Instantiate (instantiatePrim semantics)
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
            tliftToBoolSrc
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
