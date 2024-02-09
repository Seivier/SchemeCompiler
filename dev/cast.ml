open Printf
open Ast

(** Core AST **)

(* primitive operators *)
type cprim1 = Not

type cprim2 =
  | Add
  | (* Sub | Or | *) Lte
  | Eq
  (* | Grt | Eq *)
  | Get

(* Algebraic datatype for expressions *)
type cexpr =
  | Id of string
  | Num of int64
  | Bool of bool
  | Prim1 of cprim1 * cexpr
  | Prim2 of cprim2 * cexpr * cexpr
  | Let of string * cexpr * cexpr
  | If of cexpr * cexpr * cexpr
  | Apply of string * cexpr list
  | Tuple of cexpr list
  | Set of cexpr * cexpr * cexpr
  | Lambda of string list * cexpr
  | LamApply of cexpr * cexpr list
  | LetRec of (string * string list * cexpr) list * cexpr

type cfundef =
  | DefFun of string * string list * cexpr
  | DefSys of string * ctype list * ctype

let cfundef_name (f : cfundef) : string =
  match f with DefFun (n, _, _) -> n | DefSys (n, _, _) -> n

let cfundef_arity (f : cfundef) : int =
  match f with
  | DefFun (_, args, _) -> List.length args
  | DefSys (_, args, _) -> List.length args

(* Program including definitions and a body *)
type cprog = cfundef list * cexpr

(* Pretty printing expressions - used by testing framework *)
let rec string_of_cexpr (e : cexpr) : string =
  match e with
  | Num n -> Int64.to_string n
  | Bool b -> if b then "true" else "false"
  | Id s -> s
  | Prim1 (op, e) ->
      sprintf "(%s %s)" (match op with Not -> "not") (string_of_cexpr e)
  | Prim2 (op, e1, e2) ->
      sprintf "(%s %s %s)"
        (match op with Add -> "+" | Lte -> "<=" | Eq -> "=" | Get -> "get")
        (string_of_cexpr e1) (string_of_cexpr e2)
  | Let (x, e1, e2) ->
      sprintf "(let (%s %s) %s)" x (string_of_cexpr e1) (string_of_cexpr e2)
  | If (e1, e2, e3) ->
      sprintf "(if %s %s %s)" (string_of_cexpr e1) (string_of_cexpr e2)
        (string_of_cexpr e3)
  | Apply (fe, ael) ->
      sprintf "(%s %s)" fe (String.concat " " (List.map string_of_cexpr ael))
  | Tuple cexprs -> sprintf "(tup %s)" (string_of_cexprs cexprs)
  | Set (e, k, v) ->
      sprintf "(set %s %s %s)" (string_of_cexpr e) (string_of_cexpr k)
        (string_of_cexpr v)
  | Lambda (args, body) ->
      sprintf "(lambda (%s) %s)" (String.concat " " args) (string_of_cexpr body)
  | LamApply (l, args) ->
      sprintf "(@ %s %s)" (string_of_cexpr l) (string_of_cexprs args)
  | LetRec (funs, body) ->
      sprintf "(letrec (%s) (%s))"
        (String.concat " "
           (List.map
              (fun (id, args, b) ->
                sprintf "(%s (lambda (%s) (%s)))" id (String.concat " " args)
                  (string_of_cexpr b))
              funs))
        (string_of_cexpr body)

and string_of_cexprs (e : cexpr list) : string =
  match e with
  | [] -> ""
  | h :: t -> " " ^ string_of_cexpr h ^ string_of_cexprs t

(** functions below are not used, would be used if testing the parser on defs **)

(* Pretty printing function definitions - used by testing framework *)
(* let string_of_cfundef (d : cfundef) : string = *)
(*   match d with *)
(*   | DefFun (name, arg_ids, body) -> *)
(*       sprintf "(def (%s %s) %s)" name *)
(*         (String.concat " " arg_ids) *)
(*         (string_of_cexpr body) *)
(*   | DefSys (name, arg_types, ret_type) -> *)
(*       sprintf "(defsys %s %s -> %s)" name *)
(*         (String.concat " " (List.map string_of_ctype arg_types)) *)
(*         (string_of_ctype ret_type) *)

(* Pretty printing a program - used by testing framework *)
(* let string_of_prog (p : prog) : string = *)
(*   let fundefs, body = p in *)
(*   String.concat "\n" *)
(*     (List.map string_of_fundef fundefs @ [ string_of_expr body ]) *)

(* Desugaring *)
let rec desugar_let_tup xs e1 e2 i : cexpr =
  match xs with
  | [] -> e2
  | hd :: tl ->
      Let
        ( hd,
          Prim2 (Get, e1, Num (Int64.of_int i)),
          desugar_let_tup tl e1 e2 (i + 1) )

(* let rec desugar_let_rec elems acc : cexpr = *)
(*   match elems with *)
(*   | [] -> acc *)
(*   | hd :: tl -> *)
(*     let name, args, body = hd in *)
(*     desugar_let_rec tl (Let (name, Lambda (args, body), acc)) *)

let rec desugar_expr (expr : expr) : cexpr =
  match expr with
  | Num n -> Num n
  | Bool b -> Bool b
  | Id s -> Id s
  | Prim1 (op, e) -> (
      let ce = desugar_expr e in
      match op with
      | Add1 -> Prim2 (Add, ce, Num 1L)
      | Sub1 -> Prim2 (Add, ce, Num (-1L))
      | Not -> Prim1 (Not, ce)
      | Print -> Apply ("print", [ ce ]))
  | Prim2 (op, e1, e2) -> (
      let ce1 = desugar_expr e1 in
      let ce2 = desugar_expr e2 in
      match op with
      | Add -> Prim2 (Add, ce1, ce2)
      | And -> If (ce1, Prim1 (Not, Prim1 (Not, ce2)), Bool false)
      | Lte -> Prim2 (Lte, ce1, ce2)
      | Get -> Prim2 (Get, ce1, ce2)
      | Eq -> Prim2 (Eq, ce1, ce2))
  | Let (x, e1, e2) -> Let (x, desugar_expr e1, desugar_expr e2)
  | LetTup (xs, e1, e2) ->
      desugar_let_tup xs (desugar_expr e1) (desugar_expr e2) 0
  | If (e1, e2, e3) -> If (desugar_expr e1, desugar_expr e2, desugar_expr e3)
  | Apply (fe, ael) -> Apply (fe, List.map desugar_expr ael)
  | Tuple exprs -> Tuple (List.map desugar_expr exprs)
  | Set (e, k, v) -> Set (desugar_expr e, desugar_expr k, desugar_expr v)
  | Lambda (args, body) -> Lambda (args, desugar_expr body)
  | LamApply (l, args) -> LamApply (desugar_expr l, List.map desugar_expr args)
  | LetRec (fdefs, body) ->
      LetRec
        ( List.map
            (fun (name, params, b) -> (name, params, desugar_expr b))
            fdefs,
          desugar_expr body )

let rec desugar (p : prog) : cprog =
  let f, e = p in
  match f with
  | [] -> ([], desugar_expr e)
  | fdef :: tl -> (
      match fdef with
      | DefFun (name, args, body) ->
          let new_fdef = DefFun (name, args, desugar_expr body) in
          let new_f, new_e = desugar (tl, e) in
          (new_fdef :: new_f, new_e)
      | DefSys (name, args, ret) ->
          let new_fdef = DefSys (name, args, ret) in
          let new_f, new_e = desugar (tl, e) in
          (new_fdef :: new_f, new_e))
