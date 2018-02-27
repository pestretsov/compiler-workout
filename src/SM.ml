open GT

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let eval_inst cnf inst =
  let (st, (s, i, o)) = cnf in
  match inst with
  | BINOP op ->
     begin
       match st with
       | y :: x :: tail ->
          ((Syntax.Expr.eval_binop op x y) :: tail, (s, i, o))
       | _ -> failwith "cannot perform BINOP"
     end
  | CONST c -> (c :: st, (s, i, o))
  | READ ->
     begin
       match i with
       | x :: tail -> (x :: st, (s, tail, o))
       | _ -> failwith "cannot perform READ"
     end
  | WRITE ->
     begin
       match st with
       | x :: tail -> (tail, (s, i, o @ [x]))
       | _ -> failwith "cannot perform WRITE"
     end
  | LD x -> ((s x) :: st, (s, i, o))
  | ST x ->
     begin
       match st with
       | z :: tail -> (tail, ((Syntax.Expr.update x z s), i, o))
       | _ -> failwith "cannot perform ST"
     end

let rec eval cnf prg =
  match prg with
  | [] -> cnf
  | i::p -> eval (eval_inst cnf i) p

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile_expr expr =
  match expr with
  | Syntax.Expr.Var x -> [LD x]
  | Syntax.Expr.Const c -> [CONST c]
  | Syntax.Expr.Binop (op, e1, e2) -> (compile_expr e1) @ (compile_expr e2) @ [BINOP op]

let rec compile stm =
  match stm with
  | Syntax.Stmt.Assign (x, e) -> (compile_expr e) @ [ST x]
  | Syntax.Stmt.Read x -> [READ] @ [ST x]
  | Syntax.Stmt.Write e -> (compile_expr e) @ [WRITE]
  | Syntax.Stmt.Seq (s1, s2) -> (compile s1) @ (compile s2)
