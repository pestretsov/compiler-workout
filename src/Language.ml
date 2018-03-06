(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
     *)
    let eval_binop op l r =
      let bool_to_int b = if b then 1 else 0 in
      match op with
      | "+"  -> l + r
      | "-"  -> l - r
      | "*"  -> l * r
      | "/"  -> l / r
      | "%"  -> l mod r
      | "<"  -> bool_to_int (l < r)
      | ">"  -> bool_to_int (l > r)
      | ">=" -> bool_to_int (l >= r)
      | "<=" -> bool_to_int (l <= r)
      | "==" -> bool_to_int (l = r)
      | "!=" -> bool_to_int (l <> r)
      | "&&" -> bool_to_int (l <> 0 && r <> 0)
      | "!!" -> bool_to_int (l <> 0 || r <> 0)
      | _    -> failwith "this operation is not supported"

    let rec eval s e =
      match e with
      | Var v -> s v
      | Const c -> c
      | Binop (op, e1, e2) -> eval_binop op (eval s e1) (eval s e2)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

     *)
    let create_binop op = fun x y -> Binop(op, x, y)

    ostap (
      parse: expr;
      expr:
        !(Ostap.Util.expr
            (fun x -> x)
            [|
              `Lefta, [ostap ("!!"), create_binop("!!");];
              `Lefta, [ostap ("&&"), create_binop("&&");];
              `Nona , [ostap (">="), create_binop(">=");
                       ostap (">" ), create_binop(">" );
                       ostap ("<="), create_binop("<=");
                       ostap ("<" ), create_binop("<" );
                       ostap ("!="), create_binop("!=");
                       ostap ("=="), create_binop("==");];
              `Lefta, [ostap ("+" ), create_binop("+" );
                       ostap ("-" ), create_binop("-" );];
              `Lefta, [ostap ("*" ), create_binop("*" );
                       ostap ("/" ), create_binop("/" );
                       ostap ("%" ), create_binop("%" );];
            |]
            primary
          );
      primary: x:IDENT { Var x } | n:DECIMAL { Const n } | -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval cnf stm =
      let (s, i, o) = cnf in
      match stm with
      | Read x ->
         begin
           match i with
           | z :: tail -> (Expr.update x z s, tail, o)
           | _ -> failwith "cannot perform Read"
         end
      | Write e -> (s, i, o @ [Expr.eval s e])
      | Assign (x, e) -> (Expr.update x (Expr.eval s e) s, i, o)
      | Seq (s1, s2) -> eval (eval cnf s1) s2

    (* Statement parser *)
    ostap (
      parse : seq | stmt;
      stmt  : read | write | assign;
      read  : "read" -"(" x:IDENT -")" { Read x };
      write : "write" -"(" e:!(Expr.parse) -")" { Write e };
      assign: x:IDENT -":=" e:!(Expr.parse) { Assign (x, e) };
      seq   : s1:stmt -";" s2:parse { Seq(s1, s2) }
    )
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
