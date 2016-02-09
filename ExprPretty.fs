/// Pretty printer for Starling expressions.
/// Deliberately made to look like the Z3 pretty printer.
module Starling.Pretty.Expr

open Starling.Pretty.Types
open Starling.Expr
open Starling.Utils

/// Creates an S-expression from an operator string, operand print function, and
/// sequence of operands.
let sexpr op pxs =
    Seq.map pxs
    >> scons (String op)
    >> hsep
    >> parened


/// Pretty-prints an arithmetic expression.
let rec printArithExpr =
    function
    | AConst c -> c |> constToString |> String
    | AInt i -> i |> sprintf "%i" |> String
    | AAdd xs -> sexpr "+" printArithExpr xs
    | ASub xs -> sexpr "-" printArithExpr xs
    | AMul xs -> sexpr "*" printArithExpr xs
    | ADiv (x, y) -> sexpr "/" printArithExpr [x; y]

/// Pretty-prints a Boolean expression.
and printBoolExpr =
    function
    | BConst c -> c |> constToString |> String
    | BTrue -> String "true"
    | BFalse -> String "false"
    | BAnd xs -> sexpr "and" printBoolExpr xs
    | BOr xs -> sexpr "or" printBoolExpr xs
    | BImplies (x, y) -> sexpr "=>" printBoolExpr [x; y]
    | BEq (x, y) -> sexpr "=" printExpr [x; y]
    | BGt (x, y) -> sexpr ">" printArithExpr [x; y]
    | BGe (x, y) -> sexpr ">=" printArithExpr [x; y]
    | BLe (x, y) -> sexpr "<=" printArithExpr [x; y]
    | BLt (x, y) -> sexpr "<" printArithExpr [x; y]
    | BNot x -> sexpr "not" printBoolExpr [x]

/// Pretty-prints an expression.
and printExpr =
    function
    | AExpr a -> printArithExpr a
    | BExpr b -> printBoolExpr b
