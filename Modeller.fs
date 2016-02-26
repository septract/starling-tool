module Starling.Lang.Modeller

open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Expr
open Starling.Var
open Starling.Model
open Starling.Errors.Var
open Starling.Errors.Lang.Modeller
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Sub


(*
 * Conditional views.
 *)

/// A conditional (flat or if-then-else) func.
type CFunc = 
    | ITE of BoolExpr * Multiset<CFunc> * Multiset<CFunc>
    | Func of VFunc

/// A conditional view, or multiset of CFuncs.
type CView = Multiset<CFunc>

(*
 * Control structures
 *)

/// A partially resolved command.
type PartCmd<'view> = 
    | Prim of VFunc
    | While of
        isDo : bool
        * expr : BoolExpr
        * inner : Block<'view, PartCmd<'view>>
    | ITE of
        expr : BoolExpr
        * inTrue : Block<'view, PartCmd<'view>>
        * inFalse : Block<'view, PartCmd<'view>>

(*
 * Starling imperative language semantics
 *)

/// <summary>
///   The core semantic function for the imperative language.
/// </summary>
/// <remarks>
///   <para>
///     The functions beginning with '!' have special syntax in the
///     imperative language.
///   </para>
/// </remarks>
let coreSemantics =
    // TODO(CaptainHayashi): specify this in the language (standard library?).
    // TODO(CaptainHayashi): generic functions?
    // TODO(CaptainHayashi): add shared/local/expr qualifiers to parameters?
    [ (*
       * CAS
       *)
      
      // Integer CAS
      (func "ICAS" [ ipar "destB"; ipar "destA"
                     ipar "testB"; ipar "testA"
                     ipar "set" ],
       mkAnd [ mkImplies (aEq (aUnmarked "destB") (aUnmarked "testB"))
                         (mkAnd [ aEq (aUnmarked "destA") (aUnmarked "set")
                                  aEq (aUnmarked "testA") (aUnmarked "testB") ] )
               mkImplies (mkNot (aEq (aUnmarked "destB") (aUnmarked "testB")))
                         (mkAnd [ aEq (aUnmarked "destA") (aUnmarked "destB")
                                  aEq (aUnmarked "testA") (aUnmarked "destB") ] ) ] )
      // Boolean CAS
      (func "BCAS" [ bpar "destB"; bpar "destA"
                     bpar "testB"; bpar "testA"
                     bpar "set" ],
       mkAnd [ mkImplies (bEq (bUnmarked "destB") (bUnmarked "testB"))
                         (mkAnd [ bEq (bUnmarked "destA") (bUnmarked "set")
                                  bEq (bUnmarked "testA") (bUnmarked "testB") ] )
               mkImplies (mkNot (bEq (bUnmarked "destB") (bUnmarked "testB")))
                         (mkAnd [ bEq (bUnmarked "destA") (bUnmarked "destB")
                                  bEq (bUnmarked "testA") (bUnmarked "destB") ] ) ] )

      (*
       * Atomic load
       *)
      
      // Integer load
      (func "!ILoad" [ ipar "destB"; ipar "destA"
                       ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "destA") (aUnmarked "srcB")
               aEq (aUnmarked "srcA") (aUnmarked "srcB") ] )
      // Integer load-and-increment
      (func "!ILoad++" [ ipar "destB"; ipar "destA"
                         ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "destA") (aUnmarked "srcB")
               aEq (aUnmarked "srcA") (mkAdd2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Integer load-and-decrement
      (func "!ILoad--" [ ipar "destB"; ipar "destA"
                         ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "destA") (aUnmarked "srcB")
               aEq (aUnmarked "srcA") (mkSub2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Integer increment
      (func "!I++" [ ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "srcA") (mkAdd2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Integer decrement
      (func "!I--" [ ipar "srcB"; ipar "srcA" ],
       mkAnd [ aEq (aUnmarked "srcA") (mkSub2 (aUnmarked "srcB") (AInt 1L)) ] )
      // Boolean load
      (func "!BLoad" [ bpar "destB"; bpar "destA"
                       bpar "srcB"; bpar "srcA" ],
       mkAnd [ bEq (bUnmarked "destA") (bUnmarked "srcB")
               bEq (bUnmarked "srcA") (bUnmarked "srcB") ] )

      (*
       * Atomic store
       *)

      // Integer store
      (func "!IStore" [ ipar "destB"; ipar "destA"
                        ipar "src" ],
       aEq (aUnmarked "destA") (aUnmarked "src"))
      // Boolean store
      (func "!BStore" [ bpar "destB"; bpar "destA"
                        bpar "src" ],
       bEq (bUnmarked "destA") (bUnmarked "src"))

      (*
       * Local set
       *)
       
      // Integer local set
      (func "!ILSet" [ ipar "destB"; ipar "destA"
                       ipar "src" ],
       aEq (aUnmarked "destA") (aUnmarked "src"))
      // Boolean store
      (func "!BLSet" [ bpar "destB"; bpar "destA"
                       bpar "src" ],
       bEq (bUnmarked "destA") (bUnmarked "src"))

      (*
       * Assumptions
       *)

      // Identity
      (func "Id" [], BTrue)
      // Assume
      (func "Assume" [ bpar "expr" ], bUnmarked "expr") ]


(*
 * Expression classification
 *)

/// Active pattern classifying bops as to whether they create
/// arithmetic or Boolean expressions.
let (|ArithOp|BoolOp|) = 
    function 
    | Mul | Div | Add | Sub -> ArithOp
    | Gt | Ge | Le | Lt -> BoolOp
    | Eq | Neq -> BoolOp
    | And | Or -> BoolOp

/// Active pattern classifying bops as to whether they take in
/// arithmetic, Boolean, or indeterminate operands.
let (|ArithIn|BoolIn|AnyIn|) = 
    function 
    | Mul | Div | Add | Sub -> ArithIn
    | Gt | Ge | Le | Lt -> ArithIn
    | Eq | Neq -> AnyIn
    | And | Or -> BoolIn

/// Active pattern classifying expressions as to whether they are
/// arithmetic, Boolean, or indeterminate.
let (|BoolExp|ArithExp|AnyExp|) = 
    function 
    | LV _ -> AnyExp
    | Int _ -> ArithExp
    | True | False -> BoolExp
    | Bop(BoolOp, _, _) -> BoolExp
    | Bop(ArithOp, _, _) -> ArithExp

(*
 * Expression translation
 *)

/// Converts a Starling expression of ambiguous type to a Z3 predicate using
/// the given environment.
let rec modelExpr env expr = 
    match expr with
    (* First, if we have a variable, the type of expression is
     * determined by the type of the variable.
     *)
    | LV v -> 
        (* Look-up the variable to ensure it a) exists and b) is of a
         * Boolean type.
         *)
        trial { 
            let! vt = lookupVar env v |> mapMessages ((curry Var) v)
            match vt with
            | Var.Bool _ -> return mkBoolLV v |> BExpr
            | Var.Int _ -> return mkIntLV v |> AExpr
        }
    (* We can use the active patterns above to figure out whether we
     * need to treat this expression as arithmetic or Boolean.
     *)
    | ArithExp -> modelArithExpr env expr |> lift AExpr
    | BoolExp -> modelBoolExpr env expr |> lift BExpr
    | _ -> failwith "unreachable"

/// Converts a Starling Boolean expression to a Z3 predicate using
/// the given partial model and environment.
and modelBoolExpr env expr = 
    match expr with
    | True -> BTrue |> ok
    | False -> BFalse |> ok
    | LV v -> 
        (* Look-up the variable to ensure it a) exists and b) is of a
         * Boolean type.
         *)
        trial { 
            let! vt = lookupVar env v |> mapMessages ((curry Var) v)
            match vt with
            | Var.Bool _ -> return (mkBoolLV v)
            | _ -> return! (fail <| VarNotBoolean v)
        }
    | Bop(BoolOp as op, l, r) -> 
        match op with
        | ArithIn as o -> 
            trial { 
                let! lA = modelArithExpr env l
                let! rA = modelArithExpr env r
                return (match o with
                        | Gt -> mkGt
                        | Ge -> mkGe
                        | Le -> mkLe
                        | Lt -> mkLt
                        | _ -> failwith "unreachable") lA rA
            }
        | BoolIn as o -> 
            trial { 
                let! lB = modelBoolExpr env l
                let! rB = modelBoolExpr env r
                return (match o with
                        | And -> mkAnd2
                        | Or -> mkOr2
                        | _ -> failwith "unreachable") lB rB
            }
        | AnyIn as o -> 
            trial { 
                let! lE = modelExpr env l
                let! rE = modelExpr env r
                return (match o with
                        | Eq -> mkEq
                        | Neq -> mkNeq
                        | _ -> failwith "unreachable") lE rE
            }
    | _ -> fail <| ExprNotBoolean

/// Converts a Starling arithmetic expression ot a Z3 predicate using
/// the given Z3 context.
and modelArithExpr env expr = 
    match expr with
    | Int i -> i |> AInt |> ok
    | LV v -> 
        (* Look-up the variable to ensure it a) exists and b) is of an
         * arithmetic type.
         *)
        trial { 
            let! vt = lookupVar env v |> mapMessages ((curry Var) v)
            match vt with
            | Var.Int _ -> return v |> mkIntLV
            | _ -> return! (VarNotArith v |> fail)
        }
    | Bop(ArithOp as op, l, r) -> 
        trial { 
            let! lA = modelArithExpr env l
            let! rA = modelArithExpr env r
            return (match op with
                    | Mul -> mkMul2
                    | Div -> mkDiv
                    | Add -> mkAdd2
                    | Sub -> mkSub2
                    | _ -> failwith "unreachable") lA rA
        }
    | _ -> fail <| ExprNotArith

(*
 * View definitions
 *)

/// Tries to flatten a view definition AST into a multiset.
let rec viewDefToSet = 
    function 
    | ViewDef.Func f -> [f]
    | ViewDef.Unit -> []
    | ViewDef.Join(l, r) -> joinViewDefs l r

/// Merges two sides of a view monoid in the AST into one multiset.
and joinViewDefs l r = List.append (viewDefToSet l) (viewDefToSet r)

(*
 * Views
 *)

/// Merges a list of prototype and definition parameters into one list,
/// binding the types from the former to the names from the latter.
let funcViewParMerge ppars dpars = List.map2 (fun (ty, _) name -> (ty, name)) ppars dpars

/// Produces the environment created by interpreting the DFunc with
/// name name and params dpars, using the view prototype map vpm.
let modelDFunc protos name dpars = 
    // Does this functional view name a proper view?
    match Map.tryFind name protos with
    | Some ppars -> 
        // Does it have the correct number of parameters?
        let ldpars = List.length dpars
        let lppars = List.length ppars
        if ldpars <> lppars then fail <| VDEBadParamCount(name, lppars, ldpars)
        else 
            ok <| [ { Name = name
                      Params = funcViewParMerge ppars dpars } ]
    | None -> fail <| VDENoSuchView name

/// Tries to convert a view def into its model (multiset) form.
let rec modelDView protos vd = 
    match vd with
    | ViewDef.Unit -> ok []
    | ViewDef.Func {Name = v; Params = pars} -> modelDFunc protos v pars
    | ViewDef.Join(l, r) -> trial { let! lM = modelDView protos l
                                    let! rM = modelDView protos r
                                    return List.append lM rM }

/// Produces the environment created by interpreting the viewdef vds using the
/// view prototype map vpm.
let rec localEnvOfViewDef vds = 
    vds
    |> Seq.ofList
    |> Seq.map (fun {Params = ps} -> makeVarMap ps)
    |> seqBind (fun xR s -> bind (combineMaps s) xR) Map.empty
    |> mapMessages VDEBadVars

/// Produces the variable environment for the constraint whose viewdef is v.
let envOfViewDef globals =
    localEnvOfViewDef >> bind (combineMaps globals >> mapMessages VDEGlobalVarConflict)

/// Converts a single constraint to its model form.
let modelViewDef globals vprotos { CView = av; CExpression = ae } = 
    trial { 
        let! v = modelDView vprotos av |> mapMessages (curry CEView av)
        let! e = envOfViewDef globals v |> mapMessages (curry CEView av)
        let! c = match ae with
                 | Some dae -> modelBoolExpr e dae |> lift Some |> mapMessages (curry CEExpr dae)
                 | _ -> ok None
        return { View = Multiset.ofSeq v
                 Def = c }
    }
    |> mapMessages (curry MEConstraint av)

/// Extracts the view definitions from a CollatedScript, turning each into a
/// ViewDef.
let modelViewDefs globals vprotos { Constraints = cs } = 
    cs
    |> List.map (modelViewDef globals vprotos)
    |> collect

//
// View applications
//

/// Tries to flatten a view AST into a multiset.
/// Takes an environment of local variables, and the AST itself.
let rec modelView env = 
    function
    | View.Func {Name = s; Params = pars} -> 
        trial { 
            let! pexps = pars
                         |> List.map (fun e -> 
                                e
                                |> modelExpr env
                                |> mapMessages (curry VEBadExpr e))
                         |> collect
            return [ CFunc.Func { Name = s
                                  Params = pexps } ]
                   |> Multiset.ofList
        }
    | View.If(e, l, r) -> trial { let! ez3 = modelBoolExpr env e |> mapMessages (curry VEBadExpr e)
                                  let! lvs = modelView env l
                                  let! rvs = modelView env r
                                  return (CFunc.ITE(ez3, lvs, rvs) |> Multiset.singleton) }
    | Unit -> Multiset.empty() |> ok
    | Join(l, r) -> lift2 (Multiset.append) (modelView env l) (modelView env r)

//
// Axioms
//

let (|GlobalVar|_|) gs _ (lvalue : Var.LValue) = tryLookupVar gs lvalue
let (|LocalVar|_|) _ ls (lvalue : Var.LValue) = tryLookupVar ls lvalue

/// Tries to look up the type of a variable in an environment.
/// Returns a Chessie result; failures have AEBadGlobal messages.
let lookupType env var = 
    match (tryLookupVar env var) with
    | Some ty -> ok ty
    | _ ->
        var
        |> flattenLV
        |> NotFound
        |> curry AEBadGlobal var
        |> fail

/// Converts a Boolean load to a Prim.
let modelBoolLoad globals atom dest src mode = 
    (* In a Boolean load, the destination must be LOCAL and Boolean;
     *                    the source must be a GLOBAL Boolean lvalue;
     *                    and the fetch mode must be Direct.
     *)
    match src with
    | LV s -> 
        trial { 
            let! stype = lookupType globals s
            match stype, mode with
            | Type.Int, _ -> return func "!BLoad" [ dest |> blBefore; dest |> blAfter
                                                    s |> blBefore; s |> blAfter ]
            | Type.Bool, Increment -> return! fail <| AEUnsupportedAtomic(atom, "cannot increment a Boolean global")
            | Type.Bool, Decrement -> return! fail <| AEUnsupportedAtomic(atom, "cannot decrement a Boolean global")
            | _ -> return! fail <| AETypeMismatch(Type.Bool, s, stype)
        }
    | _ -> fail <| AEUnsupportedAtomic(atom, "loads must have a lvalue source")

/// Converts an integer load to a Prim.
let modelIntLoad globals atom dest src mode = 
    (* In an integer load, the destination must be LOCAL and integral;
     *                    the source must be a GLOBAL arithmetic lvalue;
     *                    and the fetch mode is unconstrained.
     *)
    match src with
    | LV s -> 
        trial { 
            let! stype = lookupType globals s
            match stype, mode with
            | Type.Int, Direct -> return func "!ILoad" [ dest |> ilBefore; dest |> ilAfter
                                                         s |> ilBefore; s |> ilAfter ]
            | Type.Int, Increment -> return func "!ILoad++" [ dest |> ilBefore; dest |> ilAfter
                                                              s |> ilBefore; s |> ilAfter ]
            | Type.Int, Decrement -> return func "!ILoad--" [ dest |> ilBefore; dest |> ilAfter
                                                              s |> ilBefore; s |> ilAfter ]
            | _ -> return! fail <| AETypeMismatch(Type.Int, s, stype)
        }
    | _ -> fail <| AEUnsupportedAtomic(atom, "loads must have a lvalue source")

/// Converts a Boolean store to a Prim.
let modelBoolStore locals atom dest src mode = 
    (* In a Boolean store, the destination must be GLOBAL and Boolean;
     *                     the source must be LOCAL and Boolean;
     *                     and the fetch mode must be Direct.
     *)
    trial { 
        let! sxp = modelBoolExpr locals src |> mapMessages (curry AEBadExpr src)
        match mode with
        | Direct -> return func "!BStore" [ dest |> blBefore; dest |> blAfter
                                            sxp |> BExpr |> before ]
        | Increment -> return! fail <| AEUnsupportedAtomic(atom, "cannot increment an expression")
        | Decrement -> return! fail <| AEUnsupportedAtomic(atom, "cannot decrement an expression")
    }

/// Converts an integral store to a Prim.
let modelIntStore locals atom dest src mode = 
    (* In an integral store, the destination must be GLOBAL and integral;
     *                       the source must be LOCAL and integral;
     *                       and the fetch mode must be Direct.
     *)
    trial { 
        let! sxp = modelArithExpr locals src |> mapMessages (curry AEBadExpr src)
        match mode with
        | Direct -> return func "!IStore" [ dest |> ilBefore; dest |> ilAfter
                                            sxp |> AExpr |> before ]
        | Increment -> return! fail <| AEUnsupportedAtomic(atom, "cannot increment an expression")
        | Decrement -> return! fail <| AEUnsupportedAtomic(atom, "cannot decrement an expression")
    }

/// Converts a precondition and postcondition to a pair of views,
/// using the given variable environment and returning errors as AxiomErrors.
let makeAxiomConds env preAst postAst = 
    lift2 mkPair
        (modelView env preAst |> mapMessages (curry AEBadView preAst)) 
        (modelView env postAst |> mapMessages (curry AEBadView postAst))

/// Converts an atomic action to a Prim.
let rec modelAtomic gs ls atom = 
    match atom with
    | CompareAndSwap(dest, test, set) -> 
        (* In a CAS, the destination must be GLOBAL;
         *           the tester and fail destination must be LOCAL;
         *           and the to-set value must be a valid expression.
         * dest, test, and set must agree on type.
         * The type of dest and test influences how we interpret set.
         *)
        trial { 
            let! dtype = lookupType gs dest
            let! ttype = lookupType ls test
            match dtype, ttype with
            | Type.Bool, Type.Bool ->
                let! setE = modelBoolExpr ls set |> mapMessages (curry AEBadExpr set)
                return func "BCAS" [dest |> blBefore; dest |> blAfter
                                    test |> blBefore; test |> blAfter
                                    setE |> BExpr |> before]
            | Type.Int, Type.Int ->
                let! setE = modelArithExpr ls set |> mapMessages (curry AEBadExpr set)
                return func "ICAS" [dest |> ilBefore; dest |> ilAfter
                                    test |> ilBefore; test |> ilAfter
                                    setE |> AExpr |> before]
            | _ -> 
                // Oops, we have a type error.
                // Arbitrarily single out test as the cause of it.
                return! fail <| AETypeMismatch(dtype, test, ttype)
        }
    | Fetch(dest, src, mode) -> 
        (* First, determine whether we have a fetch from global to local
         * (a load), or a fetch from local to global (a store).
         * Also figure out whether we have a Boolean or arithmetic
         * version.
         * We figure this out by looking at dest.
         *)
        match dest with
        | GlobalVar gs ls (Var.Int _) -> modelIntStore ls atom dest src mode
        | GlobalVar gs ls (Var.Bool _) -> modelBoolStore ls atom dest src mode
        | LocalVar gs ls (Var.Int _) -> modelIntLoad gs atom dest src mode
        | LocalVar gs ls (Var.Bool _) -> modelBoolLoad gs atom dest src mode
        // TODO(CaptainHayashi): incorrect error here.
        | lv -> fail <| AEBadGlobal(lv, NotFound(flattenLV dest))
    | Postfix(operand, mode) -> 
        (* A Postfix is basically a Fetch with no destination, at this point.
         * Thus, the source must be GLOBAL.
         * We don't allow the Direct fetch mode, as it is useless.
         *)
        trial { 
            let! stype = lookupType gs operand
            // TODO(CaptainHayashi): sort out lvalues...
            let op = flattenLV operand
            match mode, stype with
            | Direct, _ -> return! fail <| AEUnsupportedAtomic(atom, "<var>; has no effect; use <id>; or ; for no-ops")
            | Increment, Type.Bool -> return! fail <| AEUnsupportedAtomic(atom, "cannot increment a Boolean global")
            | Decrement, Type.Bool -> return! fail <| AEUnsupportedAtomic(atom, "cannot decrement a Boolean global")
            | Increment, Type.Int -> return func "!I++" [op |> aBefore |> AExpr; op |> aAfter |> AExpr]
            | Decrement, Type.Int -> return func "!I--" [op |> aBefore |> AExpr; op |> aAfter |> AExpr]
        }
    | Id -> ok (func "Id" [])
    | Assume e ->
        modelBoolExpr ls e
        |> mapMessages (curry AEBadExpr e)
        |> lift (BExpr >> Seq.singleton >> func "Assume")
/// Converts a local variable assignment to a Prim.
and modelAssign locals l e = 
    (* We model assignments as IntLocalSet or BoolLocalSet, depending on the
     * type of l, which _must_ be in the locals set..
     * We thus also have to make sure that e is the correct type.
     *)
    trial { 
        let! ltype = lookupType locals l
        match ltype with
        | Type.Bool -> let! em = modelBoolExpr locals e |> mapMessages (curry AEBadExpr e)
                       return func "!BLSet" [ l |> blBefore; l |> blAfter
                                              em |> BExpr |> before ]
        | Type.Int -> let! em = modelArithExpr locals e |> mapMessages (curry AEBadExpr e)
                      return func "!ILSet" [ l |> ilBefore; l |> ilAfter
                                             em |> AExpr |> before ]
    }

/// Creates a partially resolved axiom for an if-then-else.
and modelITE gs ls i t f = 
    (* An ITE is not fully resolved yet.  We:
     * 0) Convert the if-statement into a Starling expression;
     * 1) Place the ITE in the axioms pile;
     * 2) Merge in the axioms from the ‘then’ block;
     * 3) Merge in the axioms from the ‘else’ block.
     *)
    trial { let! iM = modelBoolExpr ls i |> mapMessages (curry AEBadExpr i)
            (* We need to calculate the recursive axioms first, because we
            * need the inner cpairs for each to store the ITE placeholder.
            *)
            let! tM = modelBlock gs ls t
            let! fM = modelBlock gs ls f
            return ITE(iM, tM, fM) }

/// Converts a while or do-while to a PartCmd.
/// Which is being modelled is determined by the isDo parameter.
/// The list is enclosed in a Chessie result.
and modelWhile isDo gs ls e b = 
    (* A while is also not fully resolved.
     * Similarly, we convert the condition, recursively find the axioms,
     * inject a placeholder, and add in the recursive axioms.
     *)
    lift2 (fun eM bM -> PartCmd.While(isDo, eM, bM))
          (modelBoolExpr ls e |> mapMessages (curry AEBadExpr e))
          (modelBlock gs ls b)

/// Converts a command to a PartCmd.
/// The list is enclosed in a Chessie result.
and modelCommand gs ls = 
    function 
    | Atomic a -> modelAtomic gs ls a |> lift Prim
    | Assign(l, e) -> modelAssign ls l e |> lift Prim
    | Skip -> modelAtomic gs ls Id |> lift Prim
    | If(i, t, e) -> modelITE gs ls i t e
    | Command.While(e, b) -> modelWhile false gs ls e b
    | DoWhile(b, e) -> modelWhile true gs ls e b
    | c -> fail <| AEUnsupportedCommand(c, "TODO: implement")

/// Converts the view and command in a ViewedCommand.
and modelViewedCommand gs ls {Post = post; Command = command} =
    lift2 (fun postM commandM -> {Post = postM; Command = commandM})
          (post |> modelView ls |> mapMessages (curry AEBadView post))
          (command |> modelCommand gs ls)

/// Converts the views and commands in a list of ViewedCommands.
and modelViewedCommands gs ls =
    Seq.map (modelViewedCommand gs ls) >> collect

/// Converts the views and commands in a block.
/// The converted block is enclosed in a Chessie result.
and modelBlock gs ls {Pre = bPre; Contents = bContents} =
    lift2 (fun bPreM bContentsM -> {Pre = bPreM; Contents = bContentsM})
          (bPre |> modelView ls |> mapMessages (curry AEBadView bPre))
          (bContents |> modelViewedCommands gs ls)

/// Converts a method's views and commands.
/// The converted method is enclosed in a Chessie result.
let modelMethod gs ls { Signature = sg ; Body = b } = 
    // TODO(CaptainHayashi): method parameters
    b
    |> modelBlock gs ls
    |> lift (fun c -> { Signature = sg ; Body = c })
    |> mapMessages (curry MEAxiom sg.Name)

/// Converts a list of methods.
/// The list is enclosed in a Chessie result.
let modelMethods gs ls = 
    // TODO(CaptainHayashi): method parameters
    List.map (modelMethod gs ls) >> collect

/// Checks a view prototype to see if it contains duplicate parameters.
let checkViewProtoDuplicates (proto : ViewProto) = 
    proto.Params
    |> Seq.map snd
    |> findDuplicates
    |> Seq.toList
    |> function 
       | [] -> ok proto
       | ds -> List.map (fun d -> VPEDuplicateParam(proto, d)) ds |> Bad

/// Checks a view prototype and converts it to an associative pair.
let modelViewProto proto = 
    proto
    |> checkViewProtoDuplicates
    |> lift (fun pro -> (pro.Name, pro.Params))
    |> mapMessages (curry MEVProto proto)

/// Checks view prototypes and converts them to map form.
let modelViewProtos protos = 
    protos
    |> Seq.ofList
    |> Seq.map modelViewProto
    |> collect
    |> lift Map.ofSeq

/// Converts a collated script to a model.
let model collated : Result<Model<AST.Method<CView, PartCmd<CView>>, DView>, ModelError> = 
    trial { 
        let! vprotos = modelViewProtos collated.VProtos
        // Make variable maps out of the global and local variable definitions.
        let! globals = makeVarMap collated.Globals |> mapMessages MEVar
        let! locals = makeVarMap collated.Locals |> mapMessages MEVar
        let! constraints = modelViewDefs globals vprotos collated
        let! axioms = modelMethods globals locals collated.Methods
        return
            { Globals = globals
              Locals = locals
              ViewDefs = constraints
              Semantics = coreSemantics
              Axioms = axioms }
    }
