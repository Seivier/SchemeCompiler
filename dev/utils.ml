open Cast
open Asm
open Parse

type nenv = (string * string) list

let empty_nenv : nenv = []
let collapse l = List.fold_left (fun acc e -> acc @ e) [] l

(* Generate a fresh name for a temporary variable. *)
let gensym : string -> string =
  let count = ref 0 in
  fun base ->
    count := !count + 1;
    Format.sprintf "%s_%d" base !count

let rec lookup_name : string -> nenv -> string =
 fun name e ->
  match e with
  | [] -> failwith ("Identifier not found: " ^ name)
  | (n, new_n) :: rest -> if n = name then new_n else lookup_name name rest

let extend_nenv (name : string) (new_name : string) (env : nenv) : nenv =
  (name, new_name) :: env

(* Local Environment *)
type env = (string * arg) list

let empty_env : env = []

(* Cuenta la cantidad de registros guardados en el stack *)
let rec aenv_slots (env : env) : int =
  match env with
  | [] -> 1
  | (_, a) :: rest -> (
      match a with RegOffset _ -> 1 + aenv_slots rest | Reg _ -> 1 | _ -> 1)

let rec env_slots (env : env) : int =
  match env with
  | [] -> 0
  | (_, a) :: rest -> (
      match a with RegOffset _ -> 1 + env_slots rest | Reg _ -> 0 | _ -> 0)

let extend_env (name : string) (env : env) : env =
  let slot = 1 + env_slots env in
  (name, RegOffset (RBP, -1 * slot)) :: env

let extend_fvars_env (name : string) (env : env) : env =
  let slot = 3 + env_slots env in
  (name, RegOffset (R15, slot)) :: env

let extend_aenv (name : string) (env : env) : env =
  let slot = 2 + env_slots env in
  (name, RegOffset (RBP, slot)) :: env

let rec lookup_env (name : string) (env : env) : arg =
  match env with
  | [] -> raise (CTError (Printf.sprintf "Identifier not found: %s" name))
  | (n, a) :: rest -> if n = name then a else lookup_env name rest

let rec create_aenv (args : string list) (aenv : env) : env =
  let rec help (i : int) (args : string list) (aenv : env) : env =
    match args with
    | [] -> aenv
    | ae :: tl ->
        if i < List.length fun_reg then
          help (i + 1) tl ((ae, Reg (List.nth fun_reg i)) :: aenv)
        else help (i + 1) tl (extend_aenv ae aenv)
  in
  help 0 args aenv

let rec create_lenv (args : string list) (aenv : env) : env =
  let n = List.length args in
  match args with
  | [] -> aenv
  | ae :: tl ->
      if n <= List.length fun_reg then
        create_lenv tl ((ae, Reg (List.nth fun_reg (n - 1))) :: aenv)
      else create_lenv tl (extend_aenv ae aenv)

let rec extend_env_with_free_vars (e : env) (fvars : string list) : env =
  match fvars with
  | [] -> e
  | fv :: tl -> extend_env fv (extend_env_with_free_vars e tl)

(* Function Environment *)
type fenv = cfundef list

let empty_fenv : fenv =
  [
    DefSys ("type_error", [ CInt; CAny ], CAny);
    DefSys ("extra_error", [ CInt; CAny; CAny ], CAny);
    DefSys ("print", [ CAny ], CAny);
    DefSys ("try_gc", [ CAny; CAny; CAny; CAny ], CAny);
    DefSys ("set_stack_bottom", [CAny], CAny);
  ]

let rec lookup_fenv (name : string) (env : fenv) : cfundef =
  match env with
  | [] -> raise (CTError (Printf.sprintf "Undefined function: %s" name))
  | f :: fs -> if cfundef_name f = name then f else lookup_fenv name fs

let rec build_fenv (flist : cfundef list) : fenv =
  match flist with [] -> empty_fenv | f :: tl -> f :: build_fenv tl

let lookup_cexpr (e : cexpr) (env : env) : arg =
  match e with Id x -> lookup_env x env | _ -> Reg RAX

let rename (e : cexpr) : cexpr =
  let rec help e (env : nenv) =
    match e with
    | Id x -> Id (lookup_name x env)
    | Let (x, e, body) ->
        let renamed_e = help e env in
        let renamed_x = gensym x in
        let renamed_body = help body (extend_nenv x renamed_x env) in
        Let (renamed_x, renamed_e, renamed_body)
    | Prim1 (op, e) -> Prim1 (op, help e env)
    | Prim2 (op, e1, e2) -> Prim2 (op, help e1 env, help e2 env)
    | If (c, t, f) -> If (help c env, help t env, help f env)
    | Apply (id, el) -> Apply (id, List.map (fun e -> help e env) el)
    | Set (e, k, v) -> Set (help e env, help k env, help v env)
    | Tuple el -> Tuple (List.map (fun e -> help e env) el)
    | Lambda (args, body) ->
        let renamed_args = List.map (fun a -> gensym a) args in
        let renamed_body = help body (List.combine args renamed_args @ env) in
        Lambda (renamed_args, renamed_body)
    | LamApply (e, el) ->
        LamApply (help e env, List.map (fun e -> help e env) el)
    | Num _ -> e
    | Bool _ -> e
    | LetRec (funs, body) ->
        let env =
          List.combine
            (List.map (fun (id, _, _) -> id) funs)
            (List.map (fun (id, _, _) -> gensym id) funs)
          @ env
        in
        let renamed_funs =
          List.map
            (fun (id, args, body) ->
              let renamed_id = lookup_name id env in
              let renamed_args = List.map (fun a -> gensym a) args in
              let renamed_body =
                help body (List.combine args renamed_args @ env)
              in
              (renamed_id, renamed_args, renamed_body))
            funs
        in
        let renamed_body = help body env in
        LetRec (renamed_funs, renamed_body)
  in
  help e []

let rec count_lets (e : cexpr) : int =
  match e with
  | Prim1 (_, e) -> count_lets e
  | Prim2 (_, e1, e2) -> count_lets e1 + count_lets e2
  | Let (_, _, body) -> 1 + count_lets body
  | If (c, t, f) -> count_lets c + max (count_lets t) (count_lets f)
  | Apply (_, el) -> List.fold_left (fun acc e -> acc + count_lets e) 0 el
  | LetRec (funs, body) -> List.length funs + count_lets body
  | _ -> 0

let rename_fun_body (e : cexpr) (args : string list) : cexpr =
  let aenv = List.combine args args in
  let rec help e (env : nenv) =
    match e with
    | Id x -> Id (lookup_name x env)
    | Let (x, e, body) ->
        let renamed_e = help e env in
        let renamed_x = gensym x in
        let renamed_body = help body (extend_nenv x renamed_x env) in
        Let (renamed_x, renamed_e, renamed_body)
    | Prim1 (op, e) -> Prim1 (op, help e env)
    | Prim2 (op, e1, e2) -> Prim2 (op, help e1 env, help e2 env)
    | If (c, t, f) -> If (help c env, help t env, help f env)
    | Apply (id, el) -> Apply (id, List.map (fun e -> help e env) el)
    | Set (e, k, v) -> Set (help e env, help k env, help v env)
    | Tuple el -> Tuple (List.map (fun e -> help e env) el)
    | Lambda (args, body) -> Lambda (args, help body env)
    | LamApply (e, el) ->
        LamApply (help e env, List.map (fun e -> help e env) el)
    | Num _ -> e
    | Bool _ -> e
    | LetRec (funs, body) ->
        let env =
          List.combine
            (List.map (fun (id, _, _) -> id) funs)
            (List.map (fun (id, _, _) -> gensym id) funs)
          @ env
        in
        let renamed_funs =
          List.map
            (fun (id, args, body) ->
              let renamed_id = lookup_name id env in
              let renamed_body = help body env in
              (renamed_id, args, renamed_body))
            funs
        in
        let renamed_body = help body env in
        LetRec (renamed_funs, renamed_body)
  in
  help e aenv

let rec free_vars (e : cexpr) (args : string list) : string list =
  match e with
  | Id x -> if List.mem x args then [] else [ x ]
  | Let (x, e, body) ->
      let free_e = free_vars e args in
      let free_body = free_vars body (x :: args) in
      free_e @ free_body
  | Prim1 (_, e) -> free_vars e args
  | Prim2 (_, e1, e2) -> free_vars e1 args @ free_vars e2 args
  | If (c, t, f) -> free_vars c args @ free_vars t args @ free_vars f args
  | Apply (_, el) -> List.fold_left (fun acc e -> acc @ free_vars e args) [] el
  | Set (e, k, v) -> free_vars e args @ free_vars k args @ free_vars v args
  | Tuple el -> List.fold_left (fun acc e -> acc @ free_vars e args) [] el
  | Lambda (_, _) -> []
  | LamApply (e, el) ->
      free_vars e args
      @ List.fold_left (fun acc e -> acc @ free_vars e args) [] el
  | LetRec (funs, body) ->
      List.fold_left
        (fun acc (_, a, body) -> acc @ free_vars body a)
        (free_vars body args) funs
  | Num _ -> []
  | Bool _ -> []

let save_regs (ins : instruction list) : instruction list =
  let rec aux (n : int) (ins : instruction list) =
    if n = 0 then ins
    else
      [ IUnop (PUSH, Reg (List.nth fun_reg (n - 1))) ]
      @ aux (n - 1) ins
      @ [ IUnop (POP, Reg (List.nth fun_reg (n - 1))) ]
  in
  aux 6 ins
