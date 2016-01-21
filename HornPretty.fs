module Starling.Pretty.Horn

open Starling.Pretty.Types
open Starling.Expr
open Starling.Horn

/// Emits a constant, munged to work in Datalog.
let printConst = 
    function 
    | Unmarked c -> sprintf "V%sU" c |> String
    | Before c -> sprintf "V%sB" c |> String
    | After c -> sprintf "V%sA" c |> String
    | Frame(i, c) -> sprintf "V%sF%A" c i |> String

/// Decides whether to put brackets over the expression emission x,
/// given its expression as the second argument.
let maybeBracket xe x = 
    match xe with 
    | SimpleArith -> x
    | CompoundArith -> parened x

/// Emits an arithmetic expression in Datalog syntax.
let rec printArith = 
    function 
    | AConst c -> printConst c
    | AInt i -> sprintf "%d" i |> String
    // Do some reshuffling of n-ary expressions into binary ones.
    // These expressions are left-associative, so this should be sound.
    | AAdd [] -> failwith "unexpected empty addition"
    | AAdd [ x ] -> printArith x
    | AAdd [ x; y ] -> printBop "+" x y
    | AAdd(x :: y :: xs) -> printArith (AAdd((AAdd [ x; y ]) :: xs))
    | ASub [] -> failwith "unexpected empty subtraction"
    | ASub [ x ] -> printArith x
    | ASub [ x; y ] -> printBop "-" x y
    | ASub(x :: y :: xs) -> printArith (ASub((ASub [ x; y ]) :: xs))
    | AMul [] -> failwith "unexpected empty multiplication"
    | AMul [ x ] -> printArith x
    | AMul [ x; y ] -> printBop "*" x y
    | AMul(x :: y :: xs) -> printArith (AMul((AMul [ x; y ]) :: xs))
    | ADiv(x, y) -> printBop "/" x y

and printBop op x y =
    binop
        op
        (x |> printArith |> maybeBracket x)
        (y |> printArith |> maybeBracket y)

/// Emits a Horn literal.
let rec printLiteral = 
    function 
    | Pred p -> printFunc printArith p
    | And xs ->
        xs
        |> Seq.map printLiteral
        |> commaSep
        |> parened
    | Or xs ->
        xs
        |> Seq.map printLiteral
        |> semiSep
        |> parened

    | ITE (i, t, e) ->
        hsep [ printLiteral i
               String "->"
               printLiteral t
               String ";"
               printLiteral e ]
        |> parened
    | True -> String "true"
    | False -> String "false"
    | Eq(x, y) -> printBop "=" x y
    | Neq(x, y) -> printBop "=\=" x y
    | Gt(x, y) -> printBop ">" x y
    | Ge(x, y) -> printBop ">=" x y
    | Le(x, y) -> printBop "<=" x y
    | Lt(x, y) -> printBop "<" x y

/// Emits a Horn clause.
let printHorn =
    function
    | Clause (hd, bd) ->
        vsep [ hsep [ printLiteral hd
                      String ":-" ]
               bd |> Seq.map printLiteral |> (fun x -> VSep (x, String ","))
                  |> Indent
                  |> (fun x -> hjoin [x; String "."] ) ]
    | Comment str -> hsep [ String "%"; String str ]
    | QueryNaming {Name = n; Params = ps} ->
        hjoin [ String "query_naming"
                [ String n
                  ps |> Seq.map String |> commaSep |> squared
                ]
                |> commaSep |> parened
                String "." ]
                           

/// Emits a Horn clause list.
let printHorns hs = hs |> List.map printHorn |> vsep
