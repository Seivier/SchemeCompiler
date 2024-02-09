open Asm
open Ast
open Utils

let not_bool = "error_not_bool"
let not_int = "error_not_int"
let not_tup = "error_not_tuple"
let out_of_bounds = "error_out_of_bounds"

let check_carity (fdef : fundef) (args : 'a list) : bool =
  fundef_arity fdef = List.length args


let check_type_error (code: int) (a: arg) (aligned : bool) = 
  let aligned_call = 
    if (not aligned) 
      then [ICall "type_error"]
      else [
        IUnop (PUSH, Reg RAX); 
        ICall "type_error"; 
        IUnop (POP, Reg RAX);
        ]
  in
  save_regs ([
    IUnop (PUSH, Reg RAX);
    IBinop (MOV, Reg RDI, Const (Int64.of_int code));
    IBinop (MOV, Reg RSI, a);
    ]
    @ aligned_call @
    [IUnop (POP, Reg RAX);])

let check_int (a: arg) (aligned : bool) = check_type_error 1 a aligned
let check_bool (a: arg) (aligned : bool) = check_type_error 2 a aligned
let check_tuple (a: arg) (aligned : bool) = check_type_error 3 a aligned
let check_closure (a: arg) (aligned : bool) = check_type_error 4 a aligned

let check_bounds (tup: arg) (k: arg) (aligned : bool) =
  let aligned_call =
    if (not aligned) 
      then [ICall "extra_error"]
      else [
        IUnop (PUSH, Reg R9); 
        ICall "extra_error"; 
        IUnop (POP, Reg R9);
        ]
  in
  save_regs ([
    IUnop (PUSH, Reg RAX);
    IBinop (MOV, Reg RDI, Const 0x5L);
    IBinop (MOV, Reg RSI, tup);
    IBinop (MOV, Reg RDX, k);
  ]
  @ aligned_call
  @ [ IUnop (POP, Reg RAX) ])
  
let check_arity (f: arg) (k: int) (aligned : bool) = 
  let aligned_call = 
    if (aligned) 
      then [ICall "extra_error"]
      else [
        IUnop (PUSH, Reg R9); 
        ICall "extra_error"; 
        IUnop (POP, Reg R9);
        ]
  in
  [
    IUnop (PUSH, Reg RDI);
    IUnop (PUSH, Reg RSI);
    IUnop (PUSH, Reg RDX);
    IUnop (PUSH, Reg RAX);
    IBinop (MOV, Reg RDI, Const 0x6L);
    IBinop (MOV, Reg RSI, f);
    IBinop (MOV, Reg RDX, Const (Int64.of_int k));
  ]
  @
    aligned_call
  @
  [
    IUnop (POP, Reg RAX);
    IUnop (POP, Reg RDX);
    IUnop (POP, Reg RSI);
    IUnop (POP, Reg RDI);
  ]
(* let check_bool (a : arg) = *)

(*   [ *)
(*     IBinop (MOV, Reg R10, a); *)
(*     IBinop (AND, Reg R10, Const 0x0000000000000007L); *)
(*     (* mask the tag *) *)
(*     IBinop (CMP, Reg R10, Const 0x0000000000000007L); *)
(*     IBinop (MOV, Reg R10, a); *)
(*     IBranch (JNE, not_bool); *)
(*   ] *)
(**)
(* let check_int (a : arg) = *)
(*   [ *)
(*     IBinop (MOV, Reg R10, a); *)
(*     IBinop (TEST, Reg R10, Const 0x0000000000000001L); *)
(*     IBranch (JNZ, not_int); *)
(*   ] *)
(**)
(* let check_tup (a : arg) : instruction list = *)
(*   [ *)
(*     IBinop (MOV, Reg R10, a); *)
(*     IBinop (AND, Reg R10, Const 0x0000000000000007L); *)
(*     (* mask the tag *) *)
(*     IBinop (CMP, Reg R10, Const 0x0000000000000001L); *)
(*     IBinop (MOV, Reg R10, a); *)
(*     IBranch (JNE, not_tup); *)
(*   ] *)
(**)
(* let check_bounds (tup : reg) (k : arg) : instruction list = *)
(*   check_int k *)
(*   @ [ *)
(*       IBinop (MOV, Reg R10, Reg tup); *)
(*       IBinop (MOV, Reg R11, k); *)
(*       IBinop (SUB, Reg tup, Const 1L); *)
(*       (* untag tuple *) *)
(*       IBinop (SAR, k, Const 1L); *)
(*       (* untag k *) *)
(*       IBinop (CMP, k, Const 0L); *)
(*       IBranch (JL, out_of_bounds); *)
(*       IBinop (CMP, k, RegOffset (tup, 0)); *)
(*       IBranch (JGE, out_of_bounds); *)
(*     ] *)

let rec check_type (t : ctype) (a : arg) (aligned : bool) : instruction list =
  match t with
  | CBool ->
      check_bool a aligned
      @ [
          IBinop (MOV, Reg R10, Const 0x8000000000000000L);
          IBinop (AND, a, Reg R10);
          IBinop (SHR, a, Const 63L);
        ]
  | CInt ->
      check_int a aligned
      @ [
          (* IBinop (MOV, a, Reg R10); *)
          (* ITerop (SHRD, a, a, Const 1L); *)
          IBinop (SAR, a, Const 1L);
        ]
  | CTuple tps ->
      check_tuple a aligned
      @ collapse (List.mapi (fun i t -> check_type t (RegOffset (reg_of_arg a, i+1)) aligned) tps)
      @ [ IBinop (SUB, a, Const 1L) ]
  | CAny -> [] (* el tagging se hace en C *)

let check_ctype (t : ctype) (a : arg) (aligned : bool) : instruction list =
  match t with
  | CBool ->
      [
        IBinop (MOV, Reg R10, Const 0x7FFFFFFFFFFFFFFFL);
        (* ITerop (SHLD, a, a, Const 63L); *)
        IBinop (SHL, a, Const 63L);
        IBinop (OR, a, Reg R10);
      ]
      @ check_bool a aligned
  | CInt ->
      [ (* ITerop (SHLD, a, a, Const 1L); *) IBinop (SHL, a, Const 1L) ]
      @ check_int a aligned
  | CTuple tps ->  
      collapse (List.mapi (fun i t -> check_type t (RegOffset (reg_of_arg a, i+1)) aligned) tps)
    @ [ IBinop (ADD, a, Const 1L) ]
    @ check_tuple a aligned
  | CAny -> [] (* el tagging se hace en C *)

