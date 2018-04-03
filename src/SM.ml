open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)
let rec eval env ((stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | inst :: prog_tail ->
       match inst with
       | BINOP op ->
          begin
            match stack with
            | y :: x :: tail ->
               eval env ((Expr.eval_binop op x y) :: tail, c) prog_tail
            | _ -> failwith "cannot perform BINOP"
          end
       | CONST v -> eval env (v :: stack, c) prog_tail
       | READ ->
          begin
            match i with
            | x :: tail -> eval env (x :: stack, (st, tail, o)) prog_tail
            | _ -> failwith "cannot perform READ"
          end
       | WRITE ->
          begin
            match stack with
            | x :: tail -> eval env (tail, (st, i, o @ [x])) prog_tail
            | _ -> failwith "cannot perform WRITE"
          end
       | LD x -> eval env ((st x) :: stack, c) prog_tail
       | ST x ->
          begin
            match stack with
            | z :: tail -> eval env (tail, ((Expr.update x z st), i, o)) prog_tail
            | _ -> failwith "cannot perform ST"
          end
       | LABEL l -> eval env conf prog_tail
       | JMP l -> eval env conf (env#labeled l)
       | CJMP (b, l) ->
          begin
            match stack with
            | x :: tail -> if (x = 0 && b = "z" || x != 0 && b = "nz")
                           then eval env (tail, c) (env#labeled l)
                           else eval env (tail, c) prog_tail
            | _ -> failwith "stack is empty"
          end

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let label_generator =
  object
    val mutable counter = 0
    method generate =
      counter <- counter + 1;
      "l_" ^ string_of_int counter
  end

let rec compile_expr expr =
  match expr with
  | Expr.Var x -> [LD x]
  | Expr.Const c -> [CONST c]
  | Expr.Binop (op, e1, e2) -> (compile_expr e1) @ (compile_expr e2) @ [BINOP op]

let rec compile stm =
  match stm with
  | Stmt.Assign (x, e) -> (compile_expr e) @ [ST x]
  | Stmt.Read x -> [READ] @ [ST x]
  | Stmt.Write e -> (compile_expr e) @ [WRITE]
  | Stmt.Seq (s1, s2) -> (compile s1) @ (compile s2)
  | Stmt.Skip -> []
  | Stmt.If (e, s1, s2) ->
     let l_else = label_generator#generate in
     let l_fi = label_generator#generate in
     (compile_expr e) @ [CJMP ("z", l_else)] @ (compile s1) @ [JMP l_fi] @ [LABEL l_else] @ (compile s2) @ [LABEL l_fi]
  | Stmt.While (e, s) ->
     let l_expr = label_generator#generate in
     let l_od = label_generator#generate in
     [LABEL l_expr] @ (compile_expr e) @ [CJMP ("z", l_od)] @ (compile s) @ [JMP l_expr] @ [LABEL l_od]
  | Stmt.RepeatUntil (e, s) ->
     let l_repeat = label_generator#generate in
     [LABEL l_repeat] @ (compile s) @ (compile_expr e) @ [CJMP ("z", l_repeat)]
