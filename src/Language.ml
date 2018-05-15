(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec list_init iter n f =
  if iter < n
  then (f iter) :: (list_init (iter + 1) n f)
  else []

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = list_init 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))
  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
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

    let rec eval env ((st, i, o, r) as conf) expr =
      match expr with
        | Const c -> (st, i, o, Some (Value.of_int c))
        | Array xs ->
           let (st', i', o', xs') = eval_list env conf xs in
           env#definition env "$array" xs' (st', i', o', None)
        | String s -> (st, i, o, Some (Value.of_string s))
        | Var v -> (st, i, o, Some (State.eval st v))
        | Binop (op, l, r) ->
           let ((_, _, _, Some a) as conf') = eval env conf l in
           let (st', i', o', Some b) = eval env conf' r in
           (st', i', o', Some (Value.of_int (eval_binop op (Value.to_int a) (Value.to_int b))))
        | Elem (xs, expr) ->
           let (st', i', o', xs') = eval_list env conf [xs; expr] in
           env#definition env "$elem" xs' (st', i', o', None)
        | Length xs ->
           let (st', i', o', Some xs') = eval env conf xs in
           env#definition env "$length" [xs'] (st', i', o', None)
        | Call (fun_name, fun_args) ->
           let (st', i', o', args) = eval_list env conf fun_args in
           env#definition env fun_name args (st', i', o', None)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)

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
            helper
          );

      helper: var:primary xs:(-"[" id:parse -"]" { `Elem id } | "." %"length" { `Length })*
              { List.fold_left (fun xs t -> match t with `Elem id -> Elem (xs, id) | `Length -> Length xs) var xs };

      primary:
        n:DECIMAL { Const n }
      | fun_name:IDENT -"(" fun_args:!(Util.list0)[parse] -")" { Call (fun_name, fun_args) }
      | "[" elems:!(Util.list0)[parse] "]" { Array elems }
      | s:STRING { String (String.sub s 1 (String.length s-2)) }
      | c:CHAR { Const (Char.code c) }
      | x:IDENT { Var x }
      | -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt =
      let meta k s =
        match k with
        | Skip -> s
        | _ -> Seq (s, k)
      in
      match stmt with
      | Assign (x, ids, e) ->
         begin
           let (st', i', o', ids') = Expr.eval_list env conf ids in
           let (st'', i'', o'', Some n) = Expr.eval env (st', i', o', None) e in
           eval env (update st'' x n ids', i'', o'', None) Skip k
         end
      | Seq (s1, s2) -> eval env conf (meta k s2) s1
      | Skip ->
         begin
           match k with
           | Skip -> conf
           | _ -> eval env conf Skip k
         end
      | If (e, s1, s2) ->
         let (st', i', o', Some n) = Expr.eval env conf e in
         eval env (st', i', o', r) k (if (Value.to_int n) != 0 then s1 else s2)
      | While (e, s) ->
         let (st', i', o', Some n) = Expr.eval env conf e in
         let conf' = (st', i', o', r) in
         if (Value.to_int n) != 0 then eval env conf' (meta k stmt) s else eval env conf' Skip k
      | Repeat (e, s) ->
         eval env conf (meta k (While (Expr.Binop ("==", e, Expr.Const 0), s))) s
      | Call (fun_name, fun_args) ->
         eval env (Expr.eval env conf (Expr.Call (fun_name, fun_args))) Skip k
      | Return opt_res ->
         begin
           match opt_res with
           | Some res -> Expr.eval env conf res
           | _ -> (st, i, o, None)
         end

    (* Statement parser *)
    ostap (
      parse      : seq | stmt;
      stmt       : assign | skip | if' | while' | for' | repeat | fun_call | return;
      seq        : s1:stmt -";" s2:parse { Seq(s1, s2) };
      skip       : %"skip" { Skip };
      if'        : %"if" cond:!(Expr.parse)
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
      while'     : %"while" cond:!(Expr.parse) %"do" while_body:parse %"od"
                  { While (cond, while_body) };
      for'       : %"for" for_asgn:parse "," cond:!(Expr.parse) "," for_upd:parse %"do" for_body:parse %"od"
                  { Seq (for_asgn, While (cond, Seq (for_body, for_upd))) };
      repeat     : %"repeat" repeat_body:parse %"until" cond:!(Expr.parse)
                  { Repeat (cond, repeat_body) };
      fun_call   : fun_name:IDENT -"(" fun_args:!(Expr.parse)* -")" { Call(fun_name, fun_args) };
      return     : %"return" res:!(Expr.parse)? { Return res };
      assign     : arr:IDENT ids:(-"[" !(Expr.parse) -"]")* ":=" exp:!(Expr.parse) {Assign (arr, ids, exp)}
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
