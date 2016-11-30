/// <summary>
///     Backend for emitting verification conditions in Grasshopper format
/// </summary>
module Starling.Backends.Grasshopper 

open Chessie.ErrorHandling

open Starling 
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
open Starling.Core.Model
open Starling.Core.Instantiate
open Starling.Core.GuardedView

[<AutoOpen>] 
module Types =
    type Grass = Backends.Z3.Types.ZModel  
    type Error = unit 

module Pretty = 
    let printQuery = 
        Backends.Z3.Pretty.printZTerm
        // failwith "not implemented yet" 

    let printGrassError e = 
        failwith "not implemented yet" 

let grassModel (i : Backends.Z3.Types.ZModel) : Result<Grass,Error>  = 
  ok i 
  // failwith "not implemented yet" 
