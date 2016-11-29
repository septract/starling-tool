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
        { SharedVars : (TypeLiteral * string) list
          ThreadVars : (TypeLiteral * string) list
          /// <summary>
          ///     The search depth, defaulting to <c>None</c> (no search).
          /// </summary>
          /// <remarks>
          ///     <para>
          ///          No search is different from a search of depth 0:
          ///          the latter includes the empty view.
          ///     </para>
          /// </remarks>
          Search : int option
          VProtos : ViewProto list
          Constraints : (ViewSignature * Expression option) list
          Methods : CMethod<Marked<View>> list }


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
              vsep <| Seq.map (uncurry printConstraint) cs.Constraints
              VSep(List.map (printMethod
                                 (printMarkedView printView)
                                 (printCommand (printMarkedView printView)))
                            cs.Methods,
                   VSkip)]

        // Add in search, but only if it actually exists.
        let all =
            match cs.Search with
            | None -> definites
            | Some s -> printSearch s :: definites

        VSep(all, (vsep [ VSkip; Separator; Nop ]))


/// <summary>
///     The empty collated script.
/// </summary>
let empty : CollatedScript =
    { Constraints = []
      Methods = []
      Search = None
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
        | SharedVars { VarType = t; VarNames = vs } ->
            // Flatten eg. 'int x, y, z' into 'int x; int y; int z'.
            let s = List.map (mkPair t) vs
            { cs with SharedVars = s @ cs.SharedVars }
        | ThreadVars { VarType = t; VarNames = vs } ->
            // Flatten eg. 'int x, y, z' into 'int x; int y; int z'.
            let s = List.map (mkPair t) vs
            { cs with ThreadVars = s @ cs.ThreadVars }
        | ViewProtos v -> { cs with VProtos = v @ cs.VProtos }
        | Search i -> { cs with Search = Some i }
        | Method m -> { cs with Methods = m::cs.Methods }
        | Constraint (v, d) -> { cs with Constraints = (v, d)::cs.Constraints }
        | Exclusive xs -> 
            let views = List.map ViewSignature.Func xs 
            { cs with Constraints = List.concat [makeExclusive views; cs.Constraints] } 
        | Disjoint xs -> 
            { cs with Constraints = List.concat [makeDisjoint xs; cs.Constraints] } 

    // We foldBack instead of fold to preserve the original order.
    List.foldBack collateStep script empty
