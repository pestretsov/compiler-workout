open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show

(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p

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
             eval env (cstack, Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) :: tail, c) prog_tail
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
     | SEXP (tag, len) ->
        let xs, stack' = split len stack in
        eval env (cstack, (Value.sexp tag (List.rev xs)) :: stack', c) prog_tail
     | DROP -> eval env (cstack, List.tl stack, c) prog_tail
     | DUP -> let v::tl = stack in eval env (cstack, v :: stack, c) prog_tail
     | SWAP -> let x::y::stack' = stack in eval env (cstack, y :: x :: stack', c) prog_tail
     | TAG t ->
        let tag::stack' = stack in
        let v = if t = Value.tag_of tag then 1 else 0 in
        eval env (cstack, Value.of_int v :: stack', c) prog_tail
     | ENTER names ->
        let values, stack' = split (List.length names) stack in
        let new_scope = List.fold_left2 (fun st x v -> State.bind x v st) State.undefined names values in
        eval env (cstack, stack', (State.push st new_scope names, i, o)) prog_tail
     | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) prog_tail
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
  (* print_prg p; *)
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

let compile (defs, p) =
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern l_false = function
   | Stmt.Pattern.Wildcard -> [DROP]
   | Stmt.Pattern.Ident _ -> [DROP]
   | Stmt.Pattern.Sexp (tag, xs) -> [DUP; TAG tag; CJMP ("z", l_false)] @ List.concat (List.mapi (fun i x -> [DUP; CONST i; CALL (".elem", 2, false)] @ pattern l_false x) xs)
   | _ -> [JMP l_false]
  and bindings p =
    let rec inner = function
    | Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident x  -> [SWAP]
    | Stmt.Pattern.Sexp (tag, xs) -> List.concat (List.mapi (fun i x -> [DUP; CONST i; CALL (".elem", 2, false)] @ inner x) xs) @ [DROP]
    in
    inner p @ [ENTER (Stmt.Pattern.vars p)]
  and expr e =
    match e with
    | Expr.Var x -> [LD x]
    | Expr.Const c -> [CONST c]
    | Expr.Binop (op, e1, e2) -> expr e1 @ expr e2 @ [BINOP op]
    | Expr.Call (fun_name, fun_args) -> call fun_name fun_args false
    | Expr.Array elems -> call ".array" elems false
    | Expr.Sexp (tag, xs) -> (List.concat (List.map expr xs)) @ [SEXP (tag, List.length xs)]
    | Expr.Elem (arr, i) -> call ".elem" [arr; i] false
    | Expr.String s -> [STRING s]
    | Expr.Length s -> call ".length" [s] false
  in
  let rec compile_stmt l env stmt =
    match stmt with
    | Stmt.Assign (x, [], e) ->
        env, false, expr e @ [ST x]
    | Stmt.Assign (x, ids, e) ->
        env, false, List.concat (List.map expr (ids @ [e])) @ [STA (x, List.length ids)]
    | Stmt.Seq (s1, s2) ->
        let env, _, code1 = compile_stmt l env s1 in
        let env, _, code2 = compile_stmt l env s2 in
        env, false, code1 @ code2
    | Stmt.Skip -> env, false, []
    | Stmt.If (e, s1, s2) ->
        let l_else, env = env#get_label in
        let l_fi, env = env#get_label in
        let env, _, true_body = compile_stmt l env s1 in
        let env, _, false_body = compile_stmt l env s2 in
        let code = (expr e) @ [CJMP ("z", l_else)] @ true_body @ [JMP l_fi; LABEL l_else] @ false_body @ [LABEL l_fi] in
        env, false, code
    | Stmt.While (e, s) ->
        let l_expr, env = env#get_label in
        let l_od, env = env#get_label in
        let env, _, body = compile_stmt l env s in
        let code = [LABEL l_expr] @ (expr e) @ [CJMP ("z", l_od)] @ body @ [JMP l_expr; LABEL l_od] in
        env, false, code
    | Stmt.Repeat (e, s) ->
        let l_repeat, env = env#get_label in
        let env, _, body = compile_stmt l env s in
        let code = [LABEL l_repeat] @ body @ (expr e) @ [CJMP ("z", l_repeat)] in
        env, false, code
    | Stmt.Call (fun_name, fun_args) ->
        env, false, call fun_name fun_args true
    | Stmt.Case (exp, branches) ->
        begin
          let l_end, env = env#get_label in
          let rec process_branches branches env ll n =
            match branches with
            | [] -> env, []
            | (patt, body)::branches' ->
              begin
                let env, _, body_compiled = compile_stmt l env body in
                let l_false, env = if n = 0 then l_end, env else env#get_label in
                let env, code = process_branches branches' env (Some l_false) (n - 1) in
                env, (match ll with None -> [] | Some l -> [LABEL l]) @ (pattern l_false patt) @ bindings patt @ body_compiled @ [LEAVE] @ (if n = 0 then [] else [JMP l_end]) @ code
              end
          in
          let env, code = process_branches branches env None (List.length branches - 1) in
          env, false, expr exp @ code @ [LABEL l_end]
        end
    | Stmt.Return opt_res ->
        begin
          match opt_res with
          | Some res -> env, false, (expr res) @ [RET true]
          | _ -> env, false, [RET false]
        end
    | Stmt.Leave -> env, false, [LEAVE]
  in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)
