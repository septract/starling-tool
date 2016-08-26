/// <summary>
///     Translator from the Starling imperative language to control-flow
///     graphs.
/// </summary>
module Starling.Lang.Grapher

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Sub
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.GuardedView
open Starling.Core.Graph
open Starling.Lang.AST
open Starling.Lang.Modeller
open Starling.Lang.Guarder.Types
open Starling.Core.Command
open Starling.Core.Command.Create

let cId : Command = List.empty
(* TODO(CaptainHayashi): currently we're assuming Assumed expressions
   are in pre-state position.  When we move to type-safe renaming this
   change should happen *here*. *)
let cAssume (expr : SMBoolExpr) : Command =
    command "Assume" [] [ simp expr |> Expr.Bool ] |> List.singleton
let cAssumeNot : SMBoolExpr -> Command = mkNot >> cAssume

/// <summary>
///     Constructs a graph from a while loop.
/// </summary>
/// <param name="vg">
///     The fresh identifier generation function to use for view IDs.
/// </param>
/// <param name="cg">
///     The fresh identifier generation function to use for edge IDs.
/// </param>
/// <param name="oP">
///     The ID of the node forming the precondition of the while loop.
/// </param>
/// <param name="oQ">
///     The ID of the node forming the postcondition of the while loop.
/// </param>
/// <param name="isDo">
///     True if this is a do-while loop; false if it is a while loop.
/// </param>
/// <param name="expr">
///     The condition expression for the while loop.
/// </param>
/// <param name="inner">
///     The block of actions inside the loop.
/// </param>
/// <returns>
///     A Chessie result containing the graph of this if statement.
/// </returns>
let rec graphWhile
  (vg : unit -> NodeID)
  (cg : unit -> EdgeID)
  (oP : NodeID)
  (oQ : EdgeID)
  (isDo : bool)
  (expr : SVBoolExpr)
  (inner : GuarderBlock)
  : Result<Subgraph, Error> =
    (* First, we need to convert the expression into an assert.
       This means we cast it into the pre-state, as it is diverging the
       program if its state _entering_ the loop condition makes expr go
       false. *)
    let _, exprB = Mapper.mapBoolCtx before NoCtx expr

    (* If isDo:
     *   Translating [|oP|] do { [|iP|] [|iQ|] } while (C) [|oQ|].
     * Else:
     *   Translating [|oP|] while (C) { [|iP|] [|iQ|] } [|oQ|].
     *)
    trial {
        // Recursively graph the block first.
        let! iP, iQ, iGraph = graphBlock false vg cg inner

        (* We presume oP and oQ are added into the nodes list by the caller,
         * and that iP and iQ are returned in iNodes.  This means the nodes
         * we return are those in iGraph.
         *)

        // Outer edges common to do-while and while loops.
        let commonEdges =
            [ // {|iQ|} assume C {|iP|}: loop back.
              (cg (), edge iQ (cAssume exprB) iP)

              // {|iQ|} assume ¬C {|oQ|}: fall out of loop.
              (cg (), edge iQ (cAssumeNot exprB) oQ) ]

        // Outer edges different between do-while and while loops.
        let diffEdges =
            if isDo
            then
                [ // {|oP|} id {|iP|}: unconditionally enter loop.
                  (cg (), edge oP cId iP) ]
            else
                [ // {|oP|} assume C {|iP|} conditionally enter loop...
                  (cg (), edge oP (cAssume exprB) iP)
                  // {|oP|} assume ¬C {|oQ|} ...otherwise skip it.
                  (cg (), edge oP (cAssumeNot exprB) oQ) ]

        let cGraph = { Nodes = Map.empty
                       Edges = (Seq.append commonEdges diffEdges
                                |> Map.ofSeq) }

        return! combine cGraph iGraph }

/// <summary>
///     Constructs a graph from an if statement.
/// </summary>
/// <param name="vg">
///     The fresh identifier generator to use for view IDs.
/// </param>
/// <param name="cg">
///     The fresh identifier generator to use for command IDs.
/// </param>
/// <param name="oP">
///     The ID of the node forming the precondition of the if statement.
/// </param>
/// <param name="oQ">
///     The ID of the node forming the postcondition of the if statement.
/// </param>
/// <param name="expr">
///     The condition expression for the true leg of the if statement.
/// </param>
/// <param name="inTrue">
///     The block of actions inside the true leg of the if statement.
/// </param>
/// <param name="inFalse">
///     The block of actions inside the false leg of the if statement.
/// </param>
/// <returns>
///     A Chessie result containing the graph of this if statement.
/// </returns>
and graphITE
  (vg : unit -> NodeID)
  (cg : unit -> EdgeID)
  (oP : NodeID)
  (oQ : NodeID)
  (expr : SVBoolExpr)
  (inTrue : GuarderBlock)
  (inFalse : GuarderBlock)
  : Result<Subgraph, Error> =
    (* First, we need to convert the expression into an assert.
       This means we cast it into the pre-state, as it is diverging the
       program if its state _entering_ the loop condition makes expr go
       false. *)
    let _, exprB = Mapper.mapBoolCtx before NoCtx expr

    // Translating [|oP|] if (C) { [|tP|] [|tQ|] } else { [|fP|] [|fQ|] } [|oQ|].
    trial {
        (* We presume oP and oQ are added into the nodes list by the caller,
         * and that tP and tQ are returned in tGraph (and fP/fQ in fGraph).
         * This means the nodes we return are tGraph and fGraph.
         *)
        let! tP, tQ, tGraph = graphBlock false vg cg inTrue
        let! fP, fQ, fGraph = graphBlock false vg cg inFalse
        let! tfGraph = combine tGraph fGraph

        let cEdges =
            [ // {|oP|} assume C {|tP|}: enter true block
              (cg (), edge oP (cAssume exprB) tP)
              // {|tQ|} id {|oQ|}: exit true block
              (cg (), edge tQ cId oQ)
              // {|oP|} assume ¬C {|fP|}: enter false block
              (cg (), edge oP (cAssumeNot exprB) fP)
              // {|fQ|} id {|oQ|}: exit false block
              (cg (), edge fQ cId oQ) ]

        // We don't add anything into the graph here.
        let cGraph = { Nodes = Map.empty
                       Edges = Map.ofSeq cEdges }

        return! combine cGraph tfGraph }

/// <summary>
///     Creates a control-flow graph for a command.
/// </summary>
/// <param name="vg">
///     The fresh identifier generator to use for view IDs.
/// </param>
/// <param name="cg">
///     The fresh identifier generator to use for command IDs.
/// </param>
/// <param name="oP">
///     The outer precondition for the command.
/// </param>
/// <param name="oQ">
///     The outer postcondition for the command.
/// </param>
/// <param name="_arg1">
///     The command to graph.
/// </param>
and graphCommand
  (vg : unit -> NodeID)
  (cg : unit -> EdgeID)
  (oP : NodeID)
  (oQ : NodeID)
  : GuarderPartCmd -> Result<Subgraph, Error> =
    function
    | Prim cmd ->
        /// Each prim is an edge by itself, so just make a one-edge graph.
        ok { Nodes = Map.empty ; Edges = Map.ofList [(cg (), edge oP cmd oQ)] }
    | While (isDo, expr, inner) ->
        graphWhile vg cg oP oQ isDo expr inner
    | ITE (expr, inTrue, inFalse) ->
        graphITE vg cg oP oQ expr inTrue inFalse

/// <summary>
///     Performs one step in creating a control-flow graph from a block.
/// </summary>
/// <param name="last">
///     Whether or not this is the last step in the block.
/// </param>
/// <param name="vg">
///     The fresh identifier generator to use for view IDs.
/// </param>
/// <param name="cg">
///     The fresh identifier generator to use for command IDs.
/// </param>
and graphBlockStep
  (last : bool)
  (vg : unit -> NodeID)
  (cg : unit -> EdgeID)
  ((iP, oGraphR) : NodeID * Result<Subgraph, Error>)
  ({ViewedCommand.Command = cmd; Post = iQview}
     : ViewedCommand<GuarderViewExpr, GuarderPartCmd>)
  : NodeID * Result<Subgraph, Error> =
    (* We already know the precondition's ID--it's in pre.
     * However, we now need to create an ID for the postcondition.
     *)
     let iQ = vg ()

     // Add the postcondition onto the outer subgraph.
     let oGraphR2 = trial {
         let pGraph = { Nodes = Map.ofList [(iQ, (iQview, if last then Exit else Normal))]
                        Edges = Map.empty }
         let! oGraph = oGraphR
         return! combine oGraph pGraph }

     // Now that iP and iQ are in the outer subgraph, we can make the command.
     let iGraphR = graphCommand vg cg iP iQ cmd

     // Finally, extend the original graph with postcondition and inner graph.
     let oGraphR3 = trial {
         let! iGraph = iGraphR
         let! oGraph = oGraphR2
         return! combine iGraph oGraph }

     (iQ, oGraphR3)

/// <summary>
///     Constructs a control-flow graph for a block.
/// </summary>
/// <param name="topLevel">
///     Whether or not this is a top-level block.
/// </param>
/// <param name="vg">
///     The fresh identifier generator to use for view IDs.
/// </param>
/// <param name="cg">
///     The fresh identifier generator to use for command IDs.
/// </param>
and graphBlock
  (topLevel : bool)
  (vg : unit -> NodeID)
  (cg : unit -> NodeID)
  ({Pre = bPre; Contents = bContents} : GuarderBlock)
  : Result<NodeID * NodeID * Subgraph, Error> =
    // First, generate the ID for the precondition.
    let oP = vg ()

    let initState = (oP, ok { Nodes = Map.ofList [(oP, (bPre, if topLevel then Entry else Normal))]
                              Edges = Map.empty } )

    (* We flip through every entry in the block, extracting its postcondition
     * and command.  The precondition is either the postcondition of
     * the last entry or the block precondition if none exists yet.
     *
     * For each entry, we model a graph and attach it to the graph in
     * the fold state.  First, however, we must add the postcondition
     * node to said graph, so the inner command graph can safely use it.
     * Each postcondition has to have a new node ID allocated for it.
     *
     * Supposing all of these steps worked, we can place the finished axiom
     * into the axioms list, and put the postcondition in place to serve as the
     * precondition for the next line.  Otherwise, our axiom list turns into a
     * failure.
     *)
    let ((oQ, graphR), _) = bContents |> List.fold (fun (state,i) cmd -> (graphBlockStep (topLevel && bContents.Length = i) vg cg state cmd, i+1)) (initState,1)

    // Pull the whole set of returns into one Result.
    lift (fun gr -> (oP, oQ, gr)) graphR

/// <summary>
///     Constructs a control-flow graph for a method.
/// </summary>
let graphMethod
  ({ Signature = { Name = name }; Body = body } : GuarderMethod)
  : Result<Graph, Error> =
    let vgen = freshGen ()
    let viewName () = 
       getFresh vgen 
       |> fun y -> y.ToString().PadLeft(3,'0')  // pad string so sorting works. 
       |> sprintf "%s_V%s" name
    let cgen = freshGen ()
    let cmdName () = 
       getFresh cgen 
       |> fun y -> y.ToString().PadLeft(3,'0')  // pad string so sorting works. 
       |> sprintf "%s_C%s" name

    body
    |> graphBlock true viewName cmdName
    |> bind (fun (oP, oQ, gr) -> graph name gr)

/// <summary>
///     Converts a model on method ASTs to one on method CFGs.
/// </summary>
/// <param name="model">
///     The model to transform.
/// </param>
/// <returns>
///     A model whose axioms are the graphs resulting from the
///     methods of <paramref name="model"/>.
/// </returns>
let graph (model : Model<GuarderMethod, _>) : Result<Model<Graph, _>, Error> =
    tryMapAxioms graphMethod model
