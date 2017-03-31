/// <summary>
///     The stage of the Starling language frontend that assembles an AST into
///     a set of collections of like-typed items.
/// </summary>
module Starling.Lang.Collator

open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.View

open Starling.Lang.AST


/// <summary>
///     Types for the collator stage.
/// </summary>
[<AutoOpen>]
module Types =
    /// <summary>
    ///     A script whose items have been partitioned by type.
    /// </summary>
    type CollatedScript =
        { /// <summary>The list of all pragma directives found.</summary>
          Pragmata : Pragma list
          /// <summary>The shared variables declared.</summary>
          SharedVars : (TypeLiteral * string) list
          /// <summary>The thread-local variables declared.</summary>
          ThreadVars : (TypeLiteral * string) list
          /// <summary>The typedef list.</summary>
          Typedefs : (TypeLiteral * string) list
          VProtos : ViewProto list
          /// <summary>The constraint list.</summary>
          Constraints : Constraint list
          /// <summary>
          ///     Map from method names to their bodies.
          ///     <para>
          ///         At this stage, we have already dealt with the method
          ///         parameters.
          ///    </para>
          /// </summary>
          Methods : Map<string, Command list> }


/// <summary>
///     Pretty printers for the collator stage.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Core.Var.Pretty

    open Starling.Lang.AST.Pretty

    /// <summary>
    ///     Pretty-prints a collated script.
    /// </summary>
    /// <param name="cs">
    ///     The collated script to print.
    /// </param>
    /// <returns>
    ///     A pretty-printer command for printing <paramref name="cs" />.
    /// </returns>
    let printCollatedScript (cs: CollatedScript) : Doc =
        let printScriptVar cls (t, v) =
            // This is a bit of a cop-out.
            let vdc = { VarType = t; VarNames = [v] }
            hsep [ String cls; printVarDecl vdc ]

        let definites =
            [ vsep <| Seq.map (fun p -> printViewProtoList [p]) cs.VProtos
              vsep <| Seq.map (printScriptVar "shared") cs.SharedVars
              vsep <| Seq.map (printScriptVar "thread") cs.ThreadVars
              vsep <| Seq.map printConstraint cs.Constraints
              printMap Indented String printCommandBlock cs.Methods ]

        VSep(definites, (vsep [ VSkip; Separator; Nop ]))


/// <summary>
///     The empty collated script.
/// </summary>
let empty : CollatedScript =
    { Pragmata = []
      Constraints = []
      Methods = Map.empty
      Typedefs = []
      VProtos = []
      SharedVars = []
      ThreadVars = [] }


/// <summary>
///     Make a list of views mutually exclusive. 
/// </summary>
let rec makeExclusive views = 

    let makeExclusiveSingle x xs = 
       List.map 
         (fun y -> (ViewSignature.Join (x,y), Some (freshNode False))) xs  

    match views with 
    | x::xs' -> 
        List.concat [ makeExclusiveSingle x xs'; makeExclusive xs'] 
    | [] -> [] 


let rec makeDisjoint (xs : List<StrFunc>) = 

    let str2Expr (s : string) : Expression = 
      freshNode (Identifier s) 

    let makeNeqArgs 
         ({Name = fx; Params = px}: StrFunc) 
         ({Name = fy; Params = py}: StrFunc) : Expression = 
      List.zip (List.map str2Expr px) (List.map str2Expr py) 
      |> 
      List.map (fun (a,b) -> freshNode (BopExpr(Neq,a,b))) 
      |> 
      List.fold 
        (fun acc e -> freshNode (BopExpr(Or,acc,e))) 
        (freshNode False) 

    let makeJoin (x: StrFunc) (y: StrFunc)  = 
      ViewSignature.Join (ViewSignature.Func x, ViewSignature.Func y)
 
    let makeDisjointSingle x xs = 
       List.map 
         (fun y -> (makeJoin x y), Some (makeNeqArgs x y))
         xs  

    match xs with 
    | x::xs' -> 
        List.concat [ makeDisjointSingle x xs'; makeDisjoint xs'] 
    | [] -> [] 

/// <summary>
///     Desugar method parameters into thread-local variables.
/// </summary>
module ParamDesugar =
    open Starling.Collections
    open Starling.Core.Symbolic
    // TODO(CaptainHayashi): move this?
 
    /// <summary>
    ///     Rewrites a block with a variable rewriting map.
    /// </summary>
    let rec rewriteBlock (rmap : Map<string, string>) (block : Command list)
      : Command list =
        // TODO(CaptainHayashi): this is a royal mess...
        let rewriteVar n = withDefault n (rmap.TryFind n)

        let rec rewriteSymbolic s =
            List.map
                (function
                 | SymArg a -> SymArg (rewriteExpression a)
                 | SymString t -> SymString t)
                s
        and rewriteExpression expr =
            let rewriteExpression' =
                function
                | True -> True
                | False -> False
                | Num k -> Num k
                | Identifier n -> Identifier (rewriteVar n)
                | Symbolic s -> Symbolic (rewriteSymbolic s)
                | BopExpr (bop, l, r) -> BopExpr (bop, rewriteExpression l, rewriteExpression r)
                | UopExpr (uop, l) -> UopExpr (uop, rewriteExpression l)
                | ArraySubscript (arr, sub) -> ArraySubscript (rewriteExpression arr, rewriteExpression sub)
            { expr with Node = rewriteExpression' expr.Node }


        let rewriteAFunc { Name = n; Params = ps } =
            { Name = n; Params = List.map rewriteExpression ps }

        let rec rewritePrim prim =
            let rewritePrim' =
                function
                | CompareAndSwap (src, test, dest) ->
                    CompareAndSwap (rewriteExpression src, rewriteExpression test, rewriteExpression dest)
                | Fetch (l, r, fm) ->
                    Fetch (rewriteExpression l, rewriteExpression r, fm)
                | Postfix (e, fm) ->
                    Postfix (rewriteExpression e, fm)
                | Id -> Id
                | Assume e -> Assume (rewriteExpression e)
                | SymCommand sym ->
                    SymCommand (rewriteSymbolic sym)
                | Havoc v -> Havoc (rewriteVar v)
            { prim with Node = rewritePrim' prim.Node }

        let rec rewriteAtomic atom =
            let rewriteAtomic' =
                function
                | APrim p -> APrim (rewritePrim p)
                | ACond (cond = c; trueBranch = t; falseBranch = f) ->
                    ACond
                        (rewriteExpression c,
                         List.map rewriteAtomic t,
                         Option.map (List.map rewriteAtomic) f)
            { atom with Node = rewriteAtomic' atom.Node }

        let rewritePrimSet { PreLocals = ps; Atomics = ts; PostLocals = qs } =
            { PreLocals = List.map rewritePrim ps
              Atomics = List.map rewriteAtomic ts
              PostLocals = List.map rewritePrim qs }

        let rec rewriteView =
            function
            | Unit -> Unit
            | Join (l, r) -> Join (rewriteView l, rewriteView r)
            | Func f -> Func (rewriteAFunc f)
            | View.If (i, t, e) -> View.If (rewriteExpression i, rewriteView t, rewriteView e)
        and rewriteCommand cmd =
            let rewriteCommand' =
                function
                | ViewExpr v -> ViewExpr (rewriteMarkedView v)
                | Prim ps -> Prim (rewritePrimSet ps)
                | If (i, t, e) -> If (rewriteExpression i, rewriteBlock rmap t, Option.map (rewriteBlock rmap) e)
                | While (c, b) -> While (rewriteExpression c, rewriteBlock rmap b)
                | DoWhile (b, c) -> DoWhile (rewriteBlock rmap b, rewriteExpression c)
                | Blocks bs -> Blocks (List.map (rewriteBlock rmap) bs)
            { cmd with Node = rewriteCommand' cmd.Node }
        and rewriteMarkedView =
            function
            | Unmarked v -> Unmarked (rewriteView v)
            | Questioned v -> Questioned (rewriteView v)
            | Unknown -> Unknown
        List.map rewriteCommand block

    /// <summary>
    ///     Converts method parameters to thread-local variables.
    /// </summary>
    /// <param name="pars">The params to desugar.</param>
    /// <param name="pos">
    ///     The position of the method.
    ///     This is used to freshen the parameter names.
    /// </param>
    /// <param name="tvars">The existing thread variable list to extend.</params>
    /// <returns>
    ///     <paramref name="tvars"/> extended to contain the thread-local variable
    ///     equivalent of <paramref name="pars"/>, as well as a substitution map to
    ///     use to rename accesses to the thread-local variable in the method
    ///     itself.
    /// </returns>
    let desugarMethodParams
      (pars : Param list) (pos : SourcePosition) (tvars : (TypeLiteral * string) list)
      : (TypeLiteral * string) list * Map<string, string> =
        let desugarParam (tvs, tmap) par =
            // This should be fine, because users can't start names with numbers.
            let newName = sprintf "%d_%d_%s" pos.Line pos.Column par.ParamName
            ((par.ParamType, newName) :: tvs, Map.add par.ParamName newName tmap)
        List.fold desugarParam (tvars, Map.empty) pars

/// <summary>
///     Collates a script, grouping all like-typed items together.
/// </summary>
/// <param name="script">
///     The list of <c>ScriptItem</c>s to collate.
/// </param>
/// <returns>
///     The <c>CollatedScript</c> resulting from collating the
///     <c>ScriptItems</c> in <paramref name="script"/>.
/// </returns>
let collate (script : ScriptItem list) : CollatedScript =
    // TODO(CaptainHayashi): rewrite this into a recursion for perf?

    let collateStep item (cs : CollatedScript) =
        match item.Node with
        | Pragma p ->
            { cs with Pragmata = p :: cs.Pragmata }
        | Typedef (t, d) ->
            { cs with Typedefs = (t, d) :: cs.Typedefs }
        | SharedVars { VarType = t; VarNames = vs } ->
            // Flatten eg. 'int x, y, z' into 'int x; int y; int z'.
            let s = List.map (mkPair t) vs
            { cs with SharedVars = s @ cs.SharedVars }
        | ThreadVars { VarType = t; VarNames = vs } ->
            // Flatten eg. 'int x, y, z' into 'int x; int y; int z'.
            let s = List.map (mkPair t) vs
            { cs with ThreadVars = s @ cs.ThreadVars }
        | ViewProtos v -> { cs with VProtos = v @ cs.VProtos }
        | Method { Signature = sigt; Body = body } ->
            let tvars, tsubs = 
                ParamDesugar.desugarMethodParams sigt.Params item.Position cs.ThreadVars
            { cs with Methods = cs.Methods.Add(sigt.Name, ParamDesugar.rewriteBlock tsubs body)
                      ThreadVars = tvars }
        | Constraint c -> { cs with Constraints = c::cs.Constraints }

    // We foldBack instead of fold to preserve the original order.
    List.foldBack collateStep script empty
