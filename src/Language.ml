(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let fail = fun x -> failwith (Printf.sprintf "Undefined variable %s" x) in
       {g = fail; l = fail; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let update_scope s' x = fun y -> if x = y then v else s' y in
      if List.mem x s.scope then
        {g = s.g; l = update_scope s.l x; scope = s.scope}
      else
        {g = update_scope s.g x; l = s.l; scope = s.scope}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if List.mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {g = st.g; l = empty.l; scope = xs}

    (* Drops a scope *)
    let leave st st' = {g = st.g; l = st'.l; scope = st'.scope}

  end

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

    let rec eval st expr =
      match expr with
      | Var v -> State.eval st v
      | Const c -> c
      | Binop (op, e1, e2) -> eval_binop op (eval st e1) (eval st e2)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    let create_binop op = fun x y -> Binop(op, x, y)
    let parse_op_list ops = List.map (fun op -> ostap ($(op)), create_binop op) ops

    ostap (
      parse: expr;
      expr:
        !(Ostap.Util.expr
            (fun x -> x)
            [|
              `Lefta, parse_op_list ["!!"];
              `Lefta, parse_op_list ["&&"];
              `Nona , parse_op_list [">="; ">"; "<="; "<"; "!="; "=="];
              `Lefta, parse_op_list ["+"; "-"];
              `Lefta, parse_op_list ["*"; "/"; "%"];
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
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt =
      match stmt with
      | Read x ->
        begin
          match i with
          | z :: tail -> (State.update x z st, tail, o)
          | _ -> failwith "cannot perform Read"
        end
      | Write e -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e) -> (State.update x (Expr.eval st e) st, i, o)
      | Seq (s1, s2) -> eval env (eval env conf s1) s2
      | Skip -> conf
      | If (e, s1, s2) -> eval env conf (if Expr.eval st e != 0 then s1 else s2)
      | While (e, s) ->
        if Expr.eval st e != 0 then eval env (eval env conf s) stmt else conf
      | Repeat (e, s) ->
        let ((st', _, _) as conf') = eval env conf s in
        if Expr.eval st' e = 0 then eval env conf' stmt else conf'
      | Call (fun_name, fun_args) ->
        let (fun_params, fun_locals, fun_body) = env#definition fun_name in
        let st' = State.enter st (fun_params @ fun_locals) in
        let assign_vals = fun acc_st param exp -> State.update param (Expr.eval st exp) acc_st in
        let fun_st = List.fold_left2 assign_vals st' fun_params fun_args in
        let (res_st, res_i, res_o) = eval env (fun_st, i, o) fun_body in
        ((State.leave res_st st), res_i, res_o)

    (* Statement parser *)
    ostap (
      parse    : seq | stmt;
      stmt     : read | write | assign | skip | if' | while' | for' | repeat | fun_call;
      read     : %"read" -"(" x:IDENT -")" { Read x };
      write    : %"write" -"(" e:!(Expr.parse) -")" { Write e };
      assign   : x:IDENT -":=" e:!(Expr.parse) { Assign (x, e) };
      seq      : s1:stmt -";" s2:parse { Seq(s1, s2) };
      skip     : %"skip" { Skip };
      if'      : %"if" cond:!(Expr.parse)
                 %"then" then_body:parse
                  elif_bodies :(%"elif" !(Expr.parse) %"then" parse)*
                  else_body :(%"else" parse)? %"fi"
                  {
                    let else_body' = match else_body with
                    | Some t -> t
                    | None -> Skip
                    in
                    let elif_else_bodies = List.fold_right (fun (e', t') t -> If (e', t', t)) elif_bodies else_body' in
                    If (cond, then_body, elif_else_bodies)
                  };
      while'   : %"while" cond:!(Expr.parse) %"do" while_body:parse %"od"
                  { While (cond, while_body) };
      for'     : %"for" for_asgn:parse "," cond:!(Expr.parse) "," for_upd:parse %"do" for_body:parse %"od"
                  { Seq (for_asgn, While (cond, Seq (for_body, for_upd))) };
      repeat   : %"repeat" repeat_body:parse %"until" cond:!(Expr.parse)
                  { Repeat (cond, repeat_body) };
      fun_call : fun_name:IDENT -"(" fun_args:!(Expr.parse)* -")" { Call(fun_name, fun_args) }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: %"fun" fun_name:IDENT -"(" fun_params:(IDENT)* -")" fun_locals:(%"local" (IDENT)*)? -"{" s:!(Stmt.parse) -"}"
              { (fun_name, (fun_params, (match fun_locals with None -> [] | Some xs -> xs), s)) }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m = List.fold_left (fun acc_map (fun_name, fun_def) -> M.add fun_name fun_def acc_map) M.empty defs in
  let (_, _, res_o) = Stmt.eval (object method definition f = M.find f m end) (State.empty, i, []) body in
  res_o

(* Top-level parser *)
ostap (
  parse: !(Definition.parse)* !(Stmt.parse)
)
