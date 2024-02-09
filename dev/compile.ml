open Cast
open Asm
open Anf
open Utils
open Error
open Parse
open Printf

let min_int = Int64.div Int64.min_int 2L
let max_int = Int64.div Int64.max_int 2L

let compile_prim1 (op : cprim1) (aligned : bool) =
  match op with
  | Not ->
      check_bool (Reg RAX) aligned
      @ [
          IBinop (MOV, Reg RBX, Const 0x8000000000000000L);
          IBinop (XOR, Reg RAX, Reg RBX);
        ]

let compile_prim2 (op : cprim2) (aligned : bool) : instruction list =
  match op with
  | Add ->
      check_int (Reg RBX) aligned
      @ check_int (Reg RAX) aligned
      @ [ IBinop (ADD, Reg RAX, Reg RBX) ]
  | Eq ->
      let label = gensym "eq" in
      check_int (Reg RBX) aligned
      @ check_int (Reg RAX) aligned
      @ [
          IBinop (CMP, Reg RBX, Reg RAX);
          IBinop (MOV, Reg RAX, const_true);
          IBranch (JE, label);
          IBinop (MOV, Reg RAX, const_false);
          ILabel label;
        ]
  | Lte ->
      let label = gensym "lte" in
      check_int (Reg RBX) aligned
      @ check_int (Reg RAX) aligned
      @ [
          IBinop (CMP, Reg RBX, Reg RAX);
          IBinop (MOV, Reg RAX, const_true);
          IBranch (JLE, label);
          IBinop (MOV, Reg RAX, const_false);
          ILabel label;
        ]
  | Get ->
      check_tuple (Reg RBX) aligned
      @ check_bounds (Reg RBX) (Reg RAX) aligned
      @ [
          IBinop (SHL, Reg RAX, Const 0x2L);
          IBinop (SUB, Reg RBX, Const 0x1L);
          IBinop (ADD, Reg RBX, Reg RAX);
          IBinop (MOV, Reg RAX, RegOffset (RBX, 1));
        ]

let xor a b = (a || b) && not (a && b)

let compile_cfundef (f : cfundef) (argsins : instruction list list)
    (aligned : bool) : instruction list =
  let n = List.length argsins in
  let offset = if n > List.length fun_reg then n mod 2 == 0 else true in
  let push_dummy =
    if aligned == offset then [] else [ IUnop (PUSH, Reg RDI) ]
  in
  let pop_dummy = if aligned == offset then [] else [ IUnop (POP, Reg RDI) ] in
  push_dummy
  @ save_regs
      (* esto básicamente añade los MOV y PUSH correspondientes para ir guardando los resultados de compilar los argumentos *)
      (match f with
      | DefFun (name, _, _) ->
          List.fold_left
            (fun acc x -> acc @ x)
            []
            (List.rev
               (List.mapi
                  (fun i a ->
                    a
                    @
                    if i < List.length fun_reg then
                      [ IBinop (MOV, Reg (List.nth fun_reg i), Reg RAX) ]
                    else [ IUnop (PUSH, Reg RAX) ])
                  argsins))
          @ [ ICall name ]
      | DefSys (name, lt, rt) ->
          List.fold_left
            (fun acc x -> acc @ x)
            []
            (List.rev
               (List.mapi
                  (fun i (a, ct) ->
                    a
                    @ check_type ct (Reg RAX) true
                    @
                    if i < List.length fun_reg then
                      [ IBinop (MOV, Reg (List.nth fun_reg i), Reg RAX) ]
                    else [ IUnop (PUSH, Reg RAX) ])
                  (List.combine argsins lt)))
          @ [ ICall name ]
          @ check_ctype rt (Reg RAX) true)
  @ pop_dummy
  @
  if n >= 6 then [ IBinop (ADD, Reg RSP, Const (Int64.of_int (8 * (n - 6)))) ]
  else []

let compile_lambda_apply (argins : instruction list list) (aligned : bool) :
    instruction list =
  let n = List.length argins + 1 in
  let offset = if n > List.length fun_reg then n mod 2 == 0 else true in
  let push_dummy = if aligned == offset then [] else [ IUnop (PUSH, Reg R9) ] in
  let pop_dummy = if aligned == offset then [] else [ IUnop (POP, Reg R9) ] in
  push_dummy
  @ save_regs
      ([ IBinop (MOV, Reg RDI, Reg RAX); IBinop (SUB, Reg RDI, Const 0x5L) ]
      @ collapse
          (List.rev
             (List.mapi
                (fun i a ->
                  a
                  @
                  if i + 1 < List.length fun_reg then
                    [ IBinop (MOV, Reg (List.nth fun_reg (i + 1)), Reg RAX) ]
                  else [ IUnop (PUSH, Reg RAX) ])
                argins))
      @ [ IUnop (CALL, RegOffset (RDI, 1)) ])
  @ pop_dummy

let rec compile_free_vars (i : int) (vars : string list) (env : env) :
    instruction list =
  match vars with
  | [] -> []
  | v :: tl ->
      [
        IBinop (MOV, Reg RAX, lookup_env v env);
        IBinop (MOV, RegOffset (R15, 3 + i), Reg RAX);
      ]
      @ compile_free_vars (i + 1) tl env

let rec compile_free_vars_in (i : int) (vars : string list) (env : env) :
    instruction list =
  match vars with
  | [] -> []
  | _ :: tl ->
      [
        IBinop (MOV, Reg RAX, RegOffset (RDI, 3 + i));
        IBinop (MOV, RegOffset (RBP, -1 * (i + 1)), Reg RAX);
      ]
      @ compile_free_vars_in (i + 1) tl env

let allocate (size : int) : instruction list =
  save_regs
    [
      IBinop (MOV, Reg (List.nth fun_reg 0), Reg R15);
      IBinop (MOV, Reg (List.nth fun_reg 1), Const (Int64.of_int size));
      IBinop (MOV, Reg (List.nth fun_reg 2), Reg RBP);
      IBinop (MOV, Reg (List.nth fun_reg 3), Reg RSP);
      ICall "try_gc";
    ]
  @ [ IBinop (MOV, Reg R15, Reg RAX) ]

let rec compile_cexpr (e : cexpr) (env : env) (fenv : fenv) (aligned : bool) :
    instruction list =
  match e with
  | Id x -> [ IBinop (MOV, Reg RAX, lookup_env x env) ]
  | Num n ->
      if n > max_int || n < min_int then
        raise (CTError (Printf.sprintf "Integer overflow: %Ld" n))
      else [ IBinop (MOV, Reg RAX, Const (Int64.mul n 2L)) ]
  | Bool b -> [ IBinop (MOV, Reg RAX, if b then const_true else const_false) ]
  | Tuple el ->
      let size = List.length el in
      allocate (size + 1)
      @ [
          IBinop (MOV, Reg RAX, Reg R15);
          IBinop (ADD, Reg RAX, Const 1L);
          IUnop (PUSH, Reg RAX);
          IBinop (MOV, Reg RAX, Const (Int64.of_int size));
          IBinop (MOV, RegOffset (R15, 0), Reg RAX);
        ]
      @ List.fold_left
          (fun acc i -> acc @ i)
          []
          (List.mapi
             (fun i ex ->
               compile_cexpr ex env fenv (not aligned)
               @ [ IBinop (MOV, RegOffset (R15, i + 1), Reg RAX) ])
             el)
      @ [
          (* IBinop (MOV, Reg RAX, Reg R15); *)
          (* IBinop (ADD, Reg RAX, Const 1L); *)
          IBinop (ADD, Reg R15, Const (Int64.of_int (8 * (size + 1))));
          IUnop (POP, Reg RAX);
        ]
  | Prim1 (op, e) -> compile_cexpr e env fenv aligned @ compile_prim1 op aligned
  | Prim2 (op, le, re) ->
      compile_cexpr le env fenv aligned
      @ [ IBinop (MOV, Reg RBX, Reg RAX) ]
      @ compile_cexpr re env fenv aligned
      @ compile_prim2 op aligned
  | Let (x, e, body) ->
      let benv = extend_env x env in
      compile_cexpr e env fenv aligned
      @ [ IBinop (MOV, lookup_env x benv, Reg RAX) ]
      @ compile_cexpr body benv fenv aligned
  | If (cond, thn, els) ->
      let else_label = gensym "else" in
      let done_label = gensym "done" in
      compile_cexpr cond env fenv aligned
      @ check_bool (Reg RAX) aligned
      @ [
          IBinop (MOV, Reg RBX, const_false);
          IBinop (CMP, Reg RBX, Reg RAX);
          IBranch (JE, else_label);
        ]
      @ compile_cexpr thn env fenv aligned
      @ [ IBranch (JMP, done_label); ILabel else_label ]
      @ compile_cexpr els env fenv aligned
      @ [ ILabel done_label ]
  | Apply (f, args) ->
      let fdef = lookup_fenv f fenv in
      let a = cfundef_arity fdef in
      if List.length args <> a then
        raise
          (CTError
             (Printf.sprintf
                "Arity mismatch: %s expected %d arguments but got %d" f a
                (List.length args)))
      else
        compile_cfundef fdef
          (List.map (fun a -> compile_cexpr a env fenv aligned) args)
          aligned
  | Set (e, k, v) ->
      compile_cexpr e env fenv aligned
      @ check_tuple (Reg RAX) aligned
      @ [ IBinop (MOV, Reg RBX, Reg RAX) ]
      @ compile_cexpr k env fenv aligned
      @ check_bounds (Reg RBX) (Reg RAX) aligned
      @ [
          IBinop (SUB, Reg RBX, Const 0x1L);
          IBinop (MOV, Reg R14, Reg RBX);
          IBinop (SHL, Reg RAX, Const 2L);
          IBinop (ADD, Reg RBX, Reg RAX);
        ]
      @ compile_cexpr v env fenv aligned
      @ [
          IBinop (MOV, RegOffset (RBX, 1), Reg RAX);
          IBinop (MOV, Reg RAX, Reg R14);
          IBinop (ADD, Reg RAX, Const 1L);
        ]
  | Lambda (args, body) -> compile_lambda args body env fenv
  | LamApply (f, args) ->
      compile_cexpr f env fenv aligned
      @ check_closure (Reg RAX) aligned
      @ check_arity (Reg RAX) (List.length args) aligned
      @ compile_lambda_apply
          (List.map (fun a -> compile_cexpr a env fenv aligned) args)
          aligned
  | LetRec (funs, body) ->
      let ids = List.fold_left (fun acc (i, _, _) -> i :: acc) [] funs in
      let lenv = List.fold_left (fun acc i -> extend_env i acc) env ids in
      let fins =
        List.map (fun (_, args, b) -> compile_lambda args b lenv fenv) funs
      in
      let _, pream =
        List.fold_left_map
          (fun acc (id, args, b) ->
            let n = List.length (free_vars b args) + 3 + acc in
            ( n,
              [
                IBinop (MOV, Reg RAX, Reg R15);
                IBinop (ADD, Reg RAX, Const (Int64.of_int (acc * 8)));
                IBinop (ADD, Reg RAX, Const 0x5L);
                IBinop (MOV, lookup_env id lenv, Reg RAX);
              ] ))
          0 funs
      in
      collapse pream @ collapse fins @ compile_cexpr body lenv fenv aligned

and compile_lambda (args : string list) (body : cexpr) (env : env) (fenv : fenv)
    =
  let label = gensym "lambda" in
  let arity = List.length args in
  let fvars = free_vars body args in
  let nvars = List.length fvars in
  let aenv = create_lenv (List.rev ("self" :: args)) empty_env in
  let aenv = extend_env_with_free_vars aenv fvars in
  let anf = anf body in
  let fstack = count_lets anf in
  [
    IBranch (JMP, sprintf "%s_end" label);
    ILabel label;
    (* Aca RSP esta alineado en 16 *)
    IUnop (PUSH, Reg RBP);
    IBinop (MOV, Reg RBP, Reg RSP);
  ]
  @ (if fstack + nvars > 0 then
       [ IBinop (SUB, Reg RSP, Const (Int64.of_int (8 * (fstack + nvars)))) ]
     else [])
  @ compile_free_vars_in 0 fvars aenv
  @ compile_cexpr anf aenv fenv ((fstack + nvars) mod 2 == 0)
  @ [
      IBinop (MOV, Reg RSP, Reg RBP);
      IUnop (POP, Reg RBP);
      IRet;
      ILabel (sprintf "%s_end" label);
    ]
  @ allocate (nvars + 3)
  @ [
      IBinop (MOV, Reg RAX, Reg R15);
      IBinop (ADD, Reg RAX, Const 0x5L);
      IUnop (PUSH, Reg RAX);
      IBinop (MOV, Reg RAX, Const (Int64.of_int arity));
      IBinop (MOV, RegOffset (R15, 0), Reg RAX);
      IBinop (LEA, Reg RAX, Address label);
      IBinop (MOV, RegOffset (R15, 1), Reg RAX);
      (* IBinop (MOV, RegOffset (R15, 1), Address name); *)
      IBinop (MOV, Reg RAX, Const (Int64.of_int (List.length fvars)));
      IBinop (MOV, RegOffset (R15, 2), Reg RAX);
    ]
  @ compile_free_vars 0 fvars env
  @ [
      (* IBinop (MOV, Reg RAX, Reg R15); *)
      (* IBinop (ADD, Reg RAX, Const 0x5L); *)
      IBinop (ADD, Reg R15, Const (Int64.of_int ((List.length fvars + 3) * 8)));
      IUnop (POP, Reg RAX);
    ]

let compile_cfundef_instr (ffenv : fenv) : instruction list =
  let rec help fenv (flist : fenv) =
    match fenv with
    | [] -> []
    | f :: tl -> (
        let ins = help tl flist in
        match f with
        | DefFun (name, args, body) ->
            let aenv = create_aenv args [] in
            [
              ILabel name; IUnop (PUSH, Reg RBP); IBinop (MOV, Reg RBP, Reg RSP);
            ]
            @
            let anf = anf (rename_fun_body body args) in
            let fstack = count_lets anf in
            (if fstack > 0 then
               [ IBinop (SUB, Reg RSP, Const (Int64.of_int (8 * fstack))) ]
             else [])
            @ compile_cexpr anf aenv flist (fstack mod 2 == 0)
            @ [ IBinop (MOV, Reg RSP, Reg RBP); IUnop (POP, Reg RBP); IRet ]
            @ ins
        | DefSys (_, _, _) -> ins)
  in
  help ffenv ffenv

let sysfun_prelude (env : fenv) : string =
  List.fold_left
    (fun acc f -> acc ^ Printf.sprintf "extern %s\n" (cfundef_name f))
    ""
    (List.filter (fun f -> match f with DefSys _ -> true | _ -> false) env)

let compile_prog p : string =
  let flist, e = desugar p in
  let fenv = build_fenv flist in
  let anf = anf (rename e) in
  let stack = count_lets anf in
  let aligned = stack mod 2 == 1 in
  let finstrs = compile_cfundef_instr fenv in
  let instrs = compile_cexpr anf empty_env fenv aligned in
  let prelude =
    "\nsection .text\n" ^ sysfun_prelude fenv
    ^ "global our_code_starts_here\nour_code_starts_here:"
  in
  prelude
  ^ pp_instrs
      ([
         IUnop (PUSH, Reg RBX);
         (* op bin *)
         IUnop (PUSH, Reg R15);
         (* heap pointer *)
         IUnop (PUSH, Reg R14);
         (* type checking *)
         IUnop (PUSH, Reg RBP);
         IBinop (MOV, Reg RBP, Reg RSP);
         IBinop (MOV, Reg R15, Reg RDI);
         (* IBinop (ADD, Reg R15, Const 7L); *)
         (* IBinop (MOV, Reg R11, Const 0xfffffffffffffff8L); *)
         (* IBinop (AND, Reg R15, Reg R11); *)
       ]
      @ save_regs
          [
            IBinop (MOV, Reg (List.nth fun_reg 0), Reg RBP);
            ICall "set_stack_bottom";
          ]
      @ (if stack > 0 then
           [ IBinop (SUB, Reg RSP, Const (Int64.of_int (8 * stack))) ]
         else [])
      @ instrs
      @ [
          IBinop (MOV, Reg RSP, Reg RBP);
          IUnop (POP, Reg RBP);
          IUnop (POP, Reg R14);
          IUnop (POP, Reg R15);
          IUnop (POP, Reg RBX);
          IRet;
        ]
      @ finstrs)
