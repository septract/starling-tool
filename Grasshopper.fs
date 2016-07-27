/// <summary>
///     Backend for emitting verification conditions in Grasshopper format
/// </summary>
module Starling.Backends.Grasshopper 

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Utils
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.Expr
// open Starling.Core.Sub
open Starling.Core.Model
open Starling.Core.Instantiate
open Starling.Core.GuardedView

[<AutoOpen>] 
module Types =
    type Query = unit  
    type Error = unit 

module Pretty = 
    let printQuery g = 
        failwith "not implemented yet" 

    let printGrassError e = 
        failwith "not implemented yet" 

let grassModel i = 
    failwith "not implemented yet" 
