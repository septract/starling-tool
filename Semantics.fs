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
open Starling.Core.GuardedView
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Traversal
open Starling.Core.Model
open Starling.Core.Traversal
open Starling.Core.Axiom.Types


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
        /// A stored command  has a missing semantic definition.
        | MissingDef of prim: StoredCommand
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
                [ printStoredCommand prim ]
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

/// <summary>
///     Generates a well-typed expression for a subscript of a given array.
/// </summary>
/// <param name="array">The fully typed array to subscript.</param>
/// <param name="idx">The index to subscript by.</param>
/// <returns>A well-typed <see cref="Expr"/> capturing the subscript.</returns>
let mkIdx (arr : TypedArrayExpr<Sym<Var>>) (idx : IntExpr<Sym<Var>>)
  : Expr<Sym<Var>> =
    match arr.SRec.ElementType with
    | Type.Int (ty, ()) -> Expr.Int (ty, IIdx (arr, idx))
    | Type.Bool (ty, ()) -> Expr.Bool (ty, BIdx (arr, idx))
    | Type.Array (ty, ()) -> Expr.Array (ty, AIdx (arr, idx))

/// <summary>
///     Tries to extract the variable and index path from a lvalue.
/// </summary>
let varAndIdxPath (expr : Expr<Sym<Var>>)
  : (TypedVar * IntExpr<Sym<Var>> list) option =
    // TODO(CaptainHayashi): proper doc comment.
    // TODO(CaptainHayashi): merge with type lookup stuff in Modeller?
    // TODO(CaptainHayashi): error perhaps if given a non-lvalue

    let rec getInBool bx path =
        match stripTypeRec bx with
        | BVar (Reg v) -> Some (Bool (bx.SRec, v), path)
        // Symbols are not lvalues, so we can't process them.
        | BIdx (a, i) -> getInArray a (i::path)
        | _ -> None
    and getInInt ix path =
        match stripTypeRec ix with
        | IVar (Reg v) -> Some (Int (ix.SRec, v), path)
        // Symbols are not lvalues, so we can't process them.
        | IIdx (a, i) -> getInArray a (i::path)
        | _ -> None
    and getInArray ax path =
        match stripTypeRec ax with
        | AVar (Reg v) -> Some (Array (ax.SRec, v), path)
        // Symbols are not lvalues, so we can't process them.
        | AIdx (a, i) -> getInArray a (i::path)
        | _ -> None

    match expr with
    | Int (ty, ix) -> getInInt (mkTypedSub ty ix) []
    | Bool (ty, bx) -> getInBool (mkTypedSub ty bx) []
    | Array (ty, ax) -> getInArray (mkTypedSub ty ax) [] 

/// <summary>
///     Normalises a microcode listing.
/// </summary>
/// <param name="instrs">The set of instructions to normalise.</param>
/// <returns>On success, the normalised listing (in arbitrary order).</returns>
let rec normaliseMicrocode
  (instrs : Microcode<Expr<Sym<Var>>, Sym<Var>> list)
  : Result<Microcode<TypedVar, Sym<Var>> list, Error> =
    (* The only thing normalisation affects is assignments, and it
       distributes over branches.  We first look at how to normalise
       assignments. *)
    
    let normaliseAssign l rO =
        (* Currently, only variables and array indices can be normalised,
           and both are converted to an underlying variable and index
           path. *)
        match varAndIdxPath l with
        | Some (lv, idx) ->
            let rec normaliseRhs remainingPath currentLhs currentRhs =
                (* Recursively expand every part of the index path so that
                   an index x...[a] on the LHS turns into an update
                   (x.. { a -> }). *)
                match remainingPath with
                | [] -> ok currentRhs
                | x::xs ->
                    // If we have an index path, this must be an array.
                    match currentLhs with
                    | Array (atype, alhs) ->
                        // In the above, this is x...[a].
                        let nextLhs = mkIdx (mkTypedSub atype alhs) x
                        (* TODO(MattWindsor91): this could do with being flipped
                        so it can be tail-recursive. *)
                        let recuR = normaliseRhs xs nextLhs currentRhs
                        lift
                            (fun recu ->
                                Expr.Array (atype, AUpd (alhs, x, recu)))
                            recuR
                    | _ ->
                        fail
                            (BadSemantics
                                "normaliseAssign: index path without array")

            let firstLhs = mkVarExp (mapCTyped Reg lv)

            let normalisedRhsR =
                // Havocs propagate up to the underlying variable.
                maybe (ok None) (normaliseRhs idx firstLhs >> lift Some) rO
            lift (fun r' -> Assign (lv, r')) normalisedRhsR


        | None ->
            fail (BadSemantics "assignment target is not a valid lvalue")

    let normaliseInstr instr =
        match instr with
        | Assume x -> ok (Assume x)
        | Symbol x -> ok (Symbol x)
        | Branch (c, t, f) ->
            lift2 (fun t' f' -> Branch (c, t', f'))
                (normaliseMicrocode t)
                (normaliseMicrocode f)
        | Assign (l, rO) -> normaliseAssign l rO

    collect (List.map normaliseInstr instrs)


let primParamSubFun
  (cmd : StoredCommand)
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
                if typesCompatible vtype (typeOf tvar)
                then ok tvar
                else fail (Inner (TypeMismatch (v, typeOf tvar)))
            | None -> fail (Inner (FreeVarInSub v)))

let checkParamCountPrim (prim : StoredCommand) (def : PrimSemantics) : Result<PrimSemantics, Error> =
    let fn = List.length prim.Args
    let dn = List.length def.Args
    if fn = dn then ok def else fail (CountMismatch (fn, dn))

let lookupPrim (prim : StoredCommand) (map : PrimSemanticsMap) : Result<PrimSemantics, Error>  =
    maybe
        (fail (MissingDef prim))
        (checkParamCountPrim prim)
        (map.TryFind prim.Name)

let checkParamTypesPrim (prim : StoredCommand) (sem : PrimSemantics) : Result<PrimSemantics, Error> =
    List.map2
        (fun fp dp ->
            if typesCompatible (typeOf fp) (typeOf dp)
            then ok ()
            else fail (TypeMismatch (dp, typeOf fp)))
        prim.Args
        sem.Args
    |> collect
    |> lift (fun _ -> sem)

/// <summary>
///     Lifts lvalue and rvalue traversals onto a microcode instruction.
/// </summary>
/// <param name="ltrav">The lvalue traversal to lift onto microcode.</param>
/// <param name="rtrav">The rvalue traversal to lift onto microcode.</param>
/// <typeparam name="L">The type of input lvalues.</typeparam>
/// <typeparam name="RV">The type of input rvalue variables.</typeparam>
/// <typeparam name="LO">The type of output lvalue.</typeparam>
/// <typeparam name="RVO">The type of output rvalue variables.</typeparam>
/// <typeparam name="Var">The type of context variables.</typeparam>
/// <typeparam name="Error">The type of traversal errors.</typeparam>
/// <returns>
///     A traversal that visits all of the lvalues and rvalues in a microcode
///     instruction, applying the given traversals to each.
/// </returns>
let traverseMicrocode
  (ltrav : Traversal<'L, 'LO, 'Error, 'Var>)
  (rtrav : Traversal<Expr<'RV>, Expr<'RVO>, 'Error, 'Var>)
  : Traversal<Microcode<'L, 'RV>,
              Microcode<'LO, 'RVO>, 'Error, 'Var> =
    let brtrav = traverseBoolAsExpr rtrav

    let rec tm ctx mc =
        let tml = tchainL tm id

        match mc with
        | Symbol s ->
            tchainL (tliftOverSymbolicWord rtrav) Symbol ctx s
        | Assign (lv, Some rv) ->
            tchain2 ltrav rtrav (pairMap id Some >> Assign) ctx (lv, rv)
        | Assign (lv, None) ->
            tchain ltrav (flip mkPair None >> Assign) ctx lv
        | Assume assumption -> tchain brtrav Assume ctx (mkTypedSub normalRec assumption)
        | Branch (i, t, e) -> tchain3 brtrav tml tml Branch ctx (mkTypedSub normalRec i, t, e)
    tm

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
    traverseMicrocode trav (tliftToExprSrc trav)

/// <summary>
///     Traversal that marks a microcode instruction with its pre- and
///     post-state.
/// </summary>
let rec markMicrocode
  (postMark : Var -> MarkedVar)
  (preStates : Map<TypedVar, MarkedVar>)
  : Traversal<Microcode<TypedVar, Sym<Var>>,
              Microcode<CTyped<MarkedVar>, Sym<MarkedVar>>,
              Error, 'Var> =
    // Define marker functions for lvalues and rvalues...
    let lf var = ok (postMark var)
    let rf var =
        match preStates.TryFind var with
        // TODO(CaptainHayashi): proper error
        | None ->
             fail (Inner (BadSemantics "somehow referenced variable not in scope"))
        | Some mv -> ok (withType (typeOf var) (Reg mv))

    // ...then use them in a traversal.
    let lt = tliftOverCTyped (ignoreContext lf)
    let rt = tliftToExprSrc (tliftToTypedSymVarSrc (tliftToExprDest (ignoreContext rf)))

    traverseMicrocode lt rt

/// <summary>
///     Converts a microcode instruction into a two-state Boolean predicate.
/// </summary>
let rec markedMicrocodeToBool
  (instr : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>>)
  : BoolExpr<Sym<MarkedVar>> =
    match instr with
    | Symbol s -> BVar (Sym s)
    // Havoc
    | Assign (x, None) -> BTrue
    // Deterministic assignment
    | Assign (x, Some y) -> mkEq (mkVarExp (mapCTyped Reg x)) y
    | Assume x -> x
    | Branch (i, t, e) ->
        let tX = mkAnd (List.map markedMicrocodeToBool t)
        let eX = mkAnd (List.map markedMicrocodeToBool e)
        mkAnd2 (mkImplies i tX) (mkImplies (mkNot i) eX)

/// <summary>
///     Generates a frame from a state assignment map.
/// </summary>
let makeFrame (states : Map<TypedVar, MarkedVar>) : BoolExpr<Sym<MarkedVar>> list =
    let maybeFrame (var, state) =
        match state with
        // If the variable was last assigned an After, it needs no framing.
        | After _ -> None
        // Otherwise, we need to bind After to its last assigned state.
        | _ ->
            Some
                (mkEq
                    (mkVarExp (mapCTyped (After >> Reg) var))
                    (mkVarExp (withType (typeOf var) (Reg state))))
    List.choose maybeFrame (Map.toList states)

/// <summary>
///     Given two assignment maps from opposite branches of a microcode
///     routine, generate extra microcode assignments to make the assignment
///     maps equal.
/// </summary>
/// <param name="tMap">The assignments from the 'true' branch.</param>
/// <param name="fMap">The assignments from the 'false' branch.</param>
/// <returns>
///     A triple containing the extra assignments for the true branch,
///     the extra assignments for the false branch, and the resulting
///     equal map.
/// </returns>
let mergeBranch
  (tMap : Map<TypedVar, MarkedVar>)
  (fMap : Map<TypedVar, MarkedVar>)
  : (Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
     * Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
     * Map<TypedVar, MarkedVar>) =
    let assign tvar high low =
        let ttype = typeOf tvar
        Assign (withType ttype high, Some (mkVarExp (withType ttype (Reg low))))

    // Assume that both maps have the same set of keys.
    let insertMapping (tvar, tmvar) (tx, fx, state : Map<TypedVar, MarkedVar>) =
        let fmvar = fMap.[tvar]
        match tmvar, fmvar with
        | // We shouldn't ever see goal variables here.
          (Goal _, _)
        | (_, Goal _) -> failwith "mergeBranch: unexpected 'goal' variable"
        | // Both branches are equal, so just add the record into the new state.
          (After _, After _) | (Before _, Before _) ->
            (tx, fx, state.Add (tvar, tmvar))
        | (Intermediate (x, _), Intermediate (y, _)) when x = y ->
            (tx, fx, state.Add (tvar, tmvar))
        | (* The 'true' branch assigned higher than the 'false' branch.
             Thus, the 'false' branch needs an extra assignment. *)
          (After _, _) | (_, Before _) ->
            let fx' = (assign tvar tmvar fmvar) :: fx
            (tx, fx', state.Add (tvar, tmvar))
        | (Intermediate (x, _), Intermediate (y, _)) when x > y ->
            let fx' = (assign tvar tmvar fmvar) :: fx
            (tx, fx', state.Add (tvar, tmvar))
        | // Otherwise, the 'true' branch needs the extra assignment.
          _ ->
            let tx' = (assign tvar fmvar tmvar) :: tx
            (tx', fx, state.Add (tvar, fmvar))

    Seq.foldBack insertMapping (Map.toSeq tMap) ([], [], Map.empty)

let updateState (st : Map<TypedVar, MarkedVar>) (vars : CTyped<MarkedVar> list)
  : Map<TypedVar, MarkedVar> =
    let updateOne (st' : Map<TypedVar, MarkedVar>) var =
        let uv = unmark var
        match st'.TryFind uv, valueOf var with
        (* Defensive code: try catch attempts to assign to a _lower_ state
           than previous. *)
        | None, v
        | Some (After _), (After _ as v)
        | Some (Before _), (Before _ as v)
        | Some (Before _), (Intermediate _ as v)
        | Some (Before _), (After _ as v) 
        | Some (Intermediate _), (After _ as v) ->
            st'.Add (unmark var, valueOf var)
        | Some (Intermediate (k, _)), (Intermediate (l, _) as v)
            when k <= l ->
            st'.Add (unmark var, valueOf var)
        | Some x, y ->
            failwith
                (sprintf "updateState: tried to reduce assign level from %A to %A"
                    x y)
                
    List.fold updateOne st vars

/// <summary>
///     Rewrites any intermediate variables in a microcode instruction
///     to post-state variables when the intermediate stage is the most
///     recently assigned in an assignment map.
/// </summary>
let capInstructions
  (state : Map<TypedVar, MarkedVar>)
  (instrs : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list)
  : Result<Map<TypedVar, MarkedVar>
           * Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list,
           TraversalError<Error>> =
    // TODO(MattWindsor91): proper doc comment.
    (* As above, patch up the lvalues and rvalues in the instruction, generating a
        list of variables that need replacing in the state. *)
    let capVar =
        fun ctx var ->
            match valueOf var, state.TryFind (unmark var) with
            | _, None ->
                fail (Inner (BadSemantics "somehow referenced variable not in scope"))
            | (Intermediate (k, _), Some (Intermediate (l, v))) when k > l ->
                fail (Inner (BadSemantics "assignment without corresponding map write"))
            | (Intermediate (k, _), Some (Intermediate (l, v))) when k = l ->
                lift
                    (fun ctx' -> (ctx', withType (typeOf var) (After v)))
                    (tryPushVar ctx (withType (typeOf var) (After v)))
            | _, Some (Before _) | _, Some (After _)
            | Before _, _ | After _, _
            | Intermediate _, Some (Intermediate _) -> ok (ctx, var)
            | _, Some _ ->
                fail (Inner (BadSemantics "unexpected goal variable"))
    let rt = tliftToExprSrc (tliftToTypedSymVarSrc (tchain capVar (mapCTyped Reg >> mkVarExp)))
    let R = tchainL (traverseMicrocode capVar rt) id (Vars []) instrs
    lift
        (fun (ctx, instrs') ->
            match ctx with
            | Vars modVars ->
                (updateState state modVars, instrs')
            | _ -> failwith "markMicrocode: bad context")
            R

/// <summary>
///     Normalises and marks an entire microcode routine with variable states,
///     without re-mapping all final intermediates to After.
/// </summary>
/// <param name="vars">The list of variables available to the routine.</param>
/// <param name="routine">The routine to mark.</param>
/// <returns>
///     A Chessie result, containing, on success, a pair of the marked
///     microcode routine and a map from variable post-states to their last
///     assignment in the microcode routine.  The latter is useful for
///     calculating frames.
///     The order of the routine is preserved.
/// </returns>
let processMicrocodeRoutineUncapped
  (vars : TypedVar list)
  (routine : Microcode<Expr<Sym<Var>>, Sym<Var>> list)
  : Result<( Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
             * Map<TypedVar, MarkedVar> ),
           Error> =
    (* First, normalise the listing.
       This ensures only whole variables are written to, which allows us to
       track the assignment later. *)
    let normalisedR = normaliseMicrocode routine

    (* Next, we annotate each command with the corresponding state marker.
       This is inherently recursive, because the microcode can contain
       branches. *)
    let rec markInstructions topState instrs
      : Result<Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
               * Map<TypedVar, MarkedVar>,
               TraversalError<Error>> =
        (* Generic logic to go through a traversable and, whenever we see a
           variable, mark it with according to its previous assignment stage,
           and put it in a list of variables to be possibly updated in the
           next assignment map. *)
        let markVar markFun (varFun : MarkedVar -> 'Var) (state : Map<TypedVar, MarkedVar>)
          : Traversal<TypedVar, CTyped<'Var>, Error, MarkedVar> =
            fun ctx var ->
                match state.TryFind var with
                | None ->
                     fail (Inner (BadSemantics "somehow referenced variable not in scope"))
                | Some mv ->
                    let markedVar = markFun mv
                    lift
                        (fun ctx' ->
                            (ctx', withType (typeOf var) (varFun markedVar)))
                        (tryPushVar ctx (withType (typeOf var) markedVar))

        let markRValue state ctx var = markVar id Reg state ctx var

        let markInstruction state (index, instr)
          : Result<Map<TypedVar, MarkedVar>
                   * Microcode<CTyped<MarkedVar>, Sym<MarkedVar>>,
                   TraversalError<Error>> =
            let rt =
                tliftToExprSrc
                    (tliftToTypedSymVarSrc (tliftToExprDest (markRValue state)))

            match instr with
            (* First, get all of the non-assigning instructions out of the way.
               Anything that isn't an assign contains only rvalues, which we
               can mark using the pre-state only. *)
            | Symbol s ->
                lift
                    (mkPair state)
                    (mapTraversal (tchainL (tliftOverSymbolicWord rt) Symbol) s)
            | Assume a ->
                lift
                    (mkPair state)
                    (mapTraversal
                        (tchain (traverseBoolAsExpr rt) Assume)
                        (normalBool a))
            (* Branches require a recursive mark-up with some patching up.
               Since the two branches will have different assignment maps,
               we have to inject new assignments into the branches to make them
               agree on the same map. *)
            | Branch (cond = c; trueBranch = t; falseBranch = f) ->
                let cR = mapTraversal (traverseBoolAsExpr rt) (normalBool c)
                let tR = markInstructions state t
                let fR = markInstructions state f
                lift3
                    (fun c' (tMarked, tState) (fMarked, fState) ->
                        let tAdd, fAdd, state = mergeBranch tState fState
                        let instrMarked =
                            Branch (c', tMarked @ tAdd, fMarked @ fAdd)
                        (state, instrMarked))
                    cR tR fR
            (* Assignments push the lvalue one intermediate higher, or to After
               if we're on the last command.  This also means that we need an
               update to the state map. *)
            | Assign (l, r) ->
                let incMarker mv =
                    match mv with
                    | Before x -> Intermediate (0I, x)
                    | Intermediate (k, x) -> Intermediate (k + 1I, x)
                    | After _ -> failwith "markMicrocode: unexpected After"
                    | Goal _ -> failwith "markMicrocode: unexpected Goal"
                let lT = markVar incMarker id state

                let lR = lT (Vars []) l
                let rR = maybe (ok None) (mapTraversal rt >> lift Some) r

                (* The lvalue traversal will have returned variables that need
                   updating in state. *)
                lift2
                    (fun (ctx, l') r' ->
                        match ctx with
                        | Vars modVars ->
                            (updateState state modVars, Assign (l', r'))
                        | _ -> failwith "markMicrocode: bad context")
                    lR rR


        let indexed = Seq.mapi mkPair instrs
        let R = bindAccumL markInstruction topState (List.ofSeq indexed)
        lift (fun (st, xs) -> (xs, st)) R

    // To begin with, each variable is assigned its own pre-state.
    let initialState =
        Map.ofSeq (Seq.map (fun var -> (var, Before (valueOf var))) vars)

    bind
        (markInstructions initialState >> mapMessages Traversal)
        normalisedR

/// <summary>
///     Normalises and marks an entire microcode routine with variable states.
/// </summary>
/// <param name="vars">The list of variables available to the routine.</param>
/// <param name="routine">The routine to mark.</param>
/// <returns>
///     A Chessie result, containing, on success, a pair of the marked
///     microcode routine and a map from variable post-states to their last
///     assignment in the microcode routine.  The latter is useful for
///     calculating frames.
///     The order of the routine is preserved.
/// </returns>
let processMicrocodeRoutine
  (vars : TypedVar list)
  (routine : Microcode<Expr<Sym<Var>>, Sym<Var>> list)
  : Result<( Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list
             * Map<TypedVar, MarkedVar> ),
           Error> =
    let intermediateMarkedR =
        processMicrocodeRoutineUncapped vars routine

    (* The above generates a decent marking, where every assignment creates
       an intermediate variable.  However, we can go one better by replacing
       every final intermediate variable with After in a second pass. *)

    let markedR =
        bind
            (fun (instrs, finalState) ->
                mapMessages Traversal (capInstructions finalState instrs))
            intermediateMarkedR
    lift (fun (st, xs) -> (xs, st)) markedR


/// <summary>
///     Converts a processed microcode routine into a two-state Boolean predicate.
/// </summary>
let microcodeRoutineToBool
  (routine : Microcode<CTyped<MarkedVar>, Sym<MarkedVar>> list)
  (assignMap : Map<TypedVar, MarkedVar>)
  : BoolExpr<Sym<MarkedVar>> =
    let bools = List.map markedMicrocodeToBool routine
    mkAnd (makeFrame assignMap @ bools)

/// <summary>
///     Converts a primitive command to its representation as a disjoint
///     parallel composition of microcode instructions.
/// </summary>
/// <param name="semantics">The map from command to microcode schemata.</param>
/// <param name="prim">The primitive command to instantiate.</param>
/// <returns>
///     If the instantiation succeeded, the resulting list of
///     <see cref="Microcode"/> instructions.
/// </returns>
let rec instantiateToMicrocode
  (semantics : PrimSemanticsMap)
  (prim : PrimCommand)
  : Result<Microcode<Expr<Sym<Var>>, Sym<Var>> list, Error> =
    match prim with
    | SymC s ->
        (* A symbol is passed through directly. *)
        ok [ Symbol s]
    | Intrinsic s ->
        (* An intrinsic can be directly converted into microcode,
           throwing away the actual direction of the intrinsic. *)
        match s with
        | IAssign { TypeRec = ty; LValue = x; RValue = y } ->
            ok [ Expr.Int (ty, x) *<- Expr.Int (ty, y) ]
        | BAssign { TypeRec = ty; LValue = x; RValue = y } ->
            ok [ Expr.Bool (ty, x) *<- Expr.Bool (ty, y) ]
        | Havoc var ->
            (* A havoc is converted to an expression. *)
            ok [ havoc (mkVarExp (mapCTyped Reg var)) ]
    | Stored sc ->
        // A stored command is a lookup into a microcode table.
        let primDefR = lookupPrim sc semantics
        let typeCheckedDefR = bind (checkParamTypesPrim sc) primDefR

        let instantiate (s : PrimSemantics) =
            let subInMCode =
                    tchainL (tliftToMicrocode (primParamSubFun sc s)) id
            mapMessages Traversal (mapTraversal subInMCode s.Body)

        bind instantiate typeCheckedDefR
    | PrimBranch (cond = c; trueBranch = t; falseBranch = f) ->
        let inst =
            List.map (instantiateToMicrocode semantics)
            >> collect
            >> lift List.concat

        lift2 
            (fun tM fM -> [ Branch (c, tM, fM) ])
            (inst t)
            (maybe (ok []) inst f)

/// <summary>
///     Translates a command to a multi-state Boolean expression.
/// </summary>
/// <param name="semantics">The map from command to microcode schemata.</param>
/// <param name="svars">The shared variable environment.</param>
/// <param name="tvars">The thread-local variable environment.</param>
/// <param name="cmd">The command to instantiate.</param>
/// <returns>
///     If the instantiation succeeded, the resulting Boolean expression.
/// </returns>
let semanticsOfCommand
  (semantics : PrimSemanticsMap)
  (svars : VarMap)
  (tvars : VarMap)
  (cmd : Command) : Result<CommandSemantics<SMBoolExpr>, Error> =
    // First, get the microcode representation of each part of the command.
    let microcodeR =
        lift List.concat
            (collect (Seq.map (instantiateToMicrocode semantics) cmd))

    (* Then, normalise and mark the microcode, and get the assign map.
       This requires us to provide all variables in the environment for framing
       purposes. *)
    let vars =
        List.ofSeq
            (Seq.append
                (VarMap.toTypedVarSeq svars)
                (VarMap.toTypedVarSeq tvars))

    let processedR = bind (processMicrocodeRoutine vars) microcodeR

    // Finally, convert the microcode and assign map to a framed expression.
    let semanticsR = lift (uncurry microcodeRoutineToBool) processedR

    // Finally, collect all of these results into a CommandSemantics record.
    lift2
        (fun (processed, assigns) semantics ->
            { Cmd = cmd
              Microcode = processed
              Assigns = assigns
              Semantics = semantics })
        processedR
        semanticsR

/// Translate a model over Prims to a model over semantic expressions.
let translate
  (model : Model<GoalAxiom<Command>, 'viewdef>)
  : Result<Model<GoalAxiom<CommandSemantics<SMBoolExpr>>, 'viewdef>, Error> =
    let modelSemantics = semanticsOfCommand model.Semantics model.SharedVars model.ThreadVars
    let replaceCmd ga c = { Goal = ga.Goal; Axiom = {Pre = ga.Axiom.Pre; Post = ga.Axiom.Post; Cmd = c }}
    let transSem ga = bind (replaceCmd ga >> ok) (modelSemantics ga.Axiom.Cmd)
    tryMapAxioms transSem model
