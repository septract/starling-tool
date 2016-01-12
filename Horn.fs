/// Types for HSF/qarmc-style Horn clause scripts.
module Starling.Horn

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Expr
open Starling.Errors.Horn

/// A literal in a Datalog-style Horn clause.
/// We model Datalog terms as Starling expressions, refusing those
/// expressions not modellable in Datalog at output time.
/// Only arithmetic expressions can be modelled in HSF, so we disallow
/// Booleans.
type Literal = 
    /// A predicate.
    | Pred of Func<ArithExpr>
    | And of Literal list
    | Or of Literal list
    | True
    | False
    | ITE of Literal * Literal * Literal
    | Eq of ArithExpr * ArithExpr
    | Neq of ArithExpr * ArithExpr
    | Gt of ArithExpr * ArithExpr
    | Ge of ArithExpr * ArithExpr
    | Le of ArithExpr * ArithExpr
    | Lt of ArithExpr * ArithExpr

/// A Horn clause, in Datalog form.
type Horn = 
    { /// The head of a Horn clause.
      Head : Literal
      /// The body of a Horn clause.
      Body : Literal list }
