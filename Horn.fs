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
    | True
    | False
    | Eq of ArithExpr * ArithExpr
    | Neq of ArithExpr * ArithExpr
    | Gt of ArithExpr * ArithExpr
    | Ge of ArithExpr * ArithExpr
    | Le of ArithExpr * ArithExpr
    | Lt of ArithExpr * ArithExpr

/// A Horn clause, in Datalog form.
type Horn =
    { /// The head of a Horn clause.
      Head: Literal
      /// The body of a Horn clause.
      Body: Literal list }

/// Emits a constant, munged to work in Datalog.
let emitConst =
    function
    | Unmarked c -> sprintf "V%sU" c
    | Before c -> sprintf "V%sB" c
    | After c -> sprintf "V%sA" c
    | Frame (i, c) -> sprintf "V%sF%A" c i 

/// Decides whether to put brackets over the expression emission x,
/// given its expression as the second argument.
let maybeBracket x =
    function
    | SimpleExpr -> x
    | CompoundExpr -> sprintf "(%s)" x

/// Emits an arithmetic expression in Datalog syntax.
let rec emitArith =
    function
    | AConst c -> emitConst c |> ok
    | AInt i -> sprintf "%d" i |> ok
    // Do some reshuffling of n-ary expressions into binary ones.
    // These expressions are left-associative, so this should be sound.
    | AAdd [] -> EmptyCompoundExpr "addition" |> fail
    | AAdd [x] -> emitArith x
    | AAdd [x; y] -> emitBop "+" x y
    | AAdd (x::y::xs) -> emitArith (AAdd ((AAdd [x; y])::xs))
    | ASub [] -> EmptyCompoundExpr "subtraction" |> fail
    | ASub [x] -> emitArith x
    | ASub [x; y] -> emitBop "-" x y
    | ASub (x::y::xs) -> emitArith (ASub ((ASub [x; y])::xs))
    | AMul [] -> EmptyCompoundExpr "multiplication" |> fail
    | AMul [x] -> emitArith x
    | AMul [x; y] -> emitBop "*" x y
    | AMul (x::y::xs) -> emitArith (AMul ((AMul [x; y])::xs))
    | ADiv (x, y) -> emitBop "/" x y

/// Emits a binary operation over two Exprs.
and emitBop op x y =
    lift2 (fun xe ye -> String.concat " " [ xe; op; ye ])
          (emitArith x)
          (emitArith y)
    
/// Emits a Horn literal.
let emitLiteral =
    function
    | Pred {Name = n; Params = ps} -> 
        ps |> Seq.map emitArith |> collect |> lift (String.concat ", " >> sprintf "%s(%s)" n)
    | True -> ok "true"
    | False -> ok "false"
    | Eq (x, y) -> emitBop "=" x y
    | Neq (x, y) -> emitBop "=\=" x y
    | Gt (x, y) -> emitBop ">" x y
    | Ge (x, y) -> emitBop ">=" x y
    | Le (x, y) -> emitBop "<=" x y
    | Lt (x, y) -> emitBop "<" x y

/// Emits a Horn clause.
let emit {Head = hd; Body = bd} =
    lift2 (sprintf "%s :- %s.")
          (emitLiteral hd)
          (bd |> Seq.map emitLiteral |> collect |> lift (String.concat ", "))
