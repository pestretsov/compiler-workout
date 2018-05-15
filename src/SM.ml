open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | inst :: prog_tail ->
     match inst with
     | BINOP op ->
        begin
          match stack with
          | y :: x :: tail ->
             eval env (cstack, Value.of_int (Expr.eval_binop op (Value.to_int x) (Value.to_int y)) :: tail, c) prog_tail
          | _ -> failwith "cannot perform BINOP"
        end
     | CONST v -> eval env (cstack, (Value.of_int v) :: stack, c) prog_tail
     | STRING s -> eval env (cstack, (Value.of_string s) :: stack, c) prog_tail
     | LD x -> eval env (cstack, (State.eval st x) :: stack, c) prog_tail
     | ST x ->
        begin
          match stack with
          | z :: tail -> eval env (cstack, tail, (State.update x z st, i, o)) prog_tail
          | _ -> failwith "cannot perform ST"
        end
     | STA (arr, len) ->
        let id::ids, stack' = split (len + 1) stack in
        eval env (cstack, stack', (Language.Stmt.update st arr id (List.rev ids), i, o)) prog_tail
     | LABEL l -> eval env conf prog_tail
     | JMP l -> eval env conf (env#labeled l)
     | CJMP (b, l) ->
        begin
            match stack with
            | x :: tail -> if ((Value.to_int x) = 0 && b = "z" || (Value.to_int x) != 0 && b = "nz")
                           then eval env (cstack, tail, c) (env#labeled l)
                           else eval env (cstack, tail, c) prog_tail
            | _ -> failwith "stack is empty"
          end
     | CALL (fun_name, args_len, is_proc) ->
        if env#is_label fun_name
        then let cstack' = ((prog_tail, st)::cstack) in eval env (cstack', stack, c) (env#labeled fun_name)
        else eval env (env#builtin conf fun_name args_len is_proc) prog_tail
     | BEGIN (_, fun_params, fun_locals) ->
        let assign_val = fun x ((v :: stack), st) -> (stack, State.update x v st) in
        let (stack', st') = List.fold_right assign_val fun_params (stack, State.enter st (fun_params @ fun_locals)) in
        eval env (cstack, stack', (st', i, o)) prog_tail
     | END | RET _ ->
        begin
          match cstack with
          | (prog, st') :: cs_tail -> eval env (cs_tail, stack, (State.leave st st', i, o)) prog
          | [] -> conf
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

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
  | Expr.Call (fun_name, fun_args) ->
     List.concat (List.map compile_expr fun_args) @ [CALL (fun_name, List.length fun_args, false)]
  | Expr.Array elems -> List.concat (List.map compile_expr elems) @ [CALL ("$array", List.length elems, false)]
  | Expr.Elem (arr, i) -> compile_expr arr @ compile_expr i @ [CALL ("$elem", 2, false)]
  | Expr.String s -> [STRING s]
  | Expr.Length s -> compile_expr s @ [CALL ("$length", 1, false)]

let rec compile_stm stm =
  match stm with
  | Stmt.Assign (x, [], e) -> (compile_expr e) @ [ST x]
  | Stmt.Assign (x, ids, e) -> List.concat (List.map compile_expr (ids @ [e])) @ [STA (x, List.length ids)]
  | Stmt.Seq (s1, s2) -> (compile_stm s1) @ (compile_stm s2)
  | Stmt.Skip -> []
  | Stmt.If (e, s1, s2) ->
     let l_else = label_generator#generate in
     let l_fi = label_generator#generate in
     (compile_expr e) @ [CJMP ("z", l_else)] @ (compile_stm s1) @ [JMP l_fi; LABEL l_else] @ (compile_stm s2) @ [LABEL l_fi]
  | Stmt.While (e, s) ->
     let l_expr = label_generator#generate in
     let l_od = label_generator#generate in
     [LABEL l_expr] @ (compile_expr e) @ [CJMP ("z", l_od)] @ (compile_stm s) @ [JMP l_expr; LABEL l_od]
  | Stmt.Repeat (e, s) ->
     let l_repeat = label_generator#generate in
     [LABEL l_repeat] @ (compile_stm s) @ (compile_expr e) @ [CJMP ("z", l_repeat)]
  | Stmt.Call (fun_name, fun_args) ->
     List.concat (List.map compile_expr (List.rev fun_args)) @ [CALL (fun_name, List.length fun_args, true)]
  | Stmt.Return opt_res ->
     begin
       match opt_res with
       | Some res -> (compile_expr res) @ [RET true]
       | _ -> [RET false]
     end

let rec compile_def (fun_name, (fun_params, fun_locals, fun_body)) =
  [LABEL fun_name; BEGIN (fun_name, fun_params, fun_locals)] @ compile_stm fun_body @ [END]

let compile (defs, p) =
  compile_stm p @ [END] @ List.concat (List.map compile_def defs)
