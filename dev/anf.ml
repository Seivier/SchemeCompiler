open Utils
open Cast

let rec is_anf : cexpr -> bool = function
  | Num _ | Bool _ | Id _ -> true
  | (Prim1 _ | Prim2 _) as e -> is_cexpr e
  | Let (_, bound_expr, body_expr) -> is_cexpr bound_expr && is_anf body_expr
  | If (cond_expr, true_expr, false_expr) ->
      is_cexpr cond_expr && is_imm true_expr && is_imm false_expr
  | Apply (_, args) -> List.for_all is_imm args
  | Tuple cexprs -> List.for_all is_imm cexprs
  | Set (ce1, ce2, ce3) -> is_cexpr ce1 && is_imm ce2 && is_imm ce3 
  | Lambda (_, body) -> is_anf body
  | LamApply (f, args) -> is_imm f && List.for_all is_imm args
  | LetRec _ -> failwith "to be implemented"  

and is_cexpr : cexpr -> bool = function
  | Num _ | Bool _ | Id _ -> true
  | Prim1 (_, expr) -> is_cexpr expr
  | Prim2 (_, expr1, expr2) -> is_imm expr1 && is_imm expr2
  | Tuple cexprs -> List.for_all is_imm cexprs
  | Let _ | If _ | Apply _ | Set _ 
  | Lambda _| LamApply _ | LetRec _ -> false


and is_imm : cexpr -> bool = function
  | Num _ | Bool _ | Id _ -> true
  | Prim1 _ | Prim2 _ | Let _ | If _ | Apply _ |Tuple _ | Set _
  | Lambda _| LamApply _ | LetRec _-> false

let rec anf (expr : cexpr) : cexpr =
  match expr with
  | (Num _ | Bool _ | Id _) as e -> e
  | Prim1 (op, expr) -> anf_c expr (fun expr -> Prim1 (op, expr))
  | Prim2 (op, expr1, expr2) ->
      anf_imm expr1 (fun expr1 ->
          anf_imm expr2 (fun expr2 -> Prim2 (op, expr1, expr2)))
  | Let (id, bound_expr, body_expr) ->
      anf_c bound_expr (fun bound_expr -> Let (id, bound_expr, anf body_expr))
  | If (cond_expr, true_expr, false_expr) ->
      If
        ( anf_c cond_expr (fun cond_expr -> cond_expr),
          anf_imm true_expr (fun true_expr -> true_expr),
          anf_imm false_expr (fun false_expr -> false_expr) )
  | Apply _ | Tuple _ | LamApply _-> anf_imm_expr expr []
  | Set (e, kval, v)  -> 
      anf_imm e (fun e -> 
        anf_imm kval (fun kval ->
          anf_imm v (fun v -> Set (e, kval, v))))
  | Lambda (args, body) -> Lambda (args, anf body)
  | LetRec _ -> anf_bindings expr []

and anf_imm (expr : cexpr) (k : cexpr -> cexpr) : cexpr =
  match expr with
  | (Num _ | Bool _ | Id _) as e -> k e
  | Prim1 (op, expr) ->
      let tmp = gensym "prim1" in
      anf_c expr (fun expr -> Let (tmp, Prim1 (op, expr), k (Id tmp)))
  | Prim2 (op, expr1, expr2) ->
      let tmp = gensym "prim2" in
      anf_imm expr1 (fun expr1 ->
          anf_imm expr2 (fun expr2 ->
              Let (tmp, Prim2 (op, expr1, expr2), k (Id tmp))))
  | Let (id, bound_expr, body_expr) ->
      anf_c bound_expr (fun bound_expr ->
          Let (id, bound_expr, anf_imm body_expr (fun body_expr -> k body_expr)))
  | If (cond_expr, true_expr, false_expr) ->
      let tmp = gensym "if" in
      Let
        ( tmp,
          If
            ( anf_c cond_expr (fun cond_expr -> cond_expr),
              anf_imm true_expr (fun true_expr -> true_expr),
              anf_imm false_expr (fun false_expr -> false_expr) ),
          k (Id tmp) )
  | Apply (f, args) ->
      let tmp = gensym "apply" in
      anf_imm_expr (Let (tmp, Apply (f, args), k (Id tmp))) []
  | Tuple el ->
      let tmp = gensym "tuple" in
        anf_imm_expr (Let (tmp, Tuple el, k (Id tmp))) []
  | Set (e, kval, v)  -> 
      let tmp = gensym "set" in
        anf_imm e (fun e -> 
          anf_imm kval (fun kval ->
            anf_imm v (fun v -> Let (tmp, Set (e, kval, v), k (Id tmp)))))
  | Lambda (args, body) -> 
      let tmp = gensym "lambda" in
        Let (tmp, Lambda (args, anf body) , k (Id tmp))
  | LamApply (f, args) -> 
      let tmp = gensym "lamapply" in
        anf_imm_expr (Let (tmp, LamApply (f, args), k (Id tmp))) []
  | LetRec (_) -> anf_imm_bindings expr [] k
and anf_c (expr : cexpr) (k : cexpr -> cexpr) : cexpr =
  match expr with
  | (Num _ | Bool _ | Id _) as e -> k e
  | Prim1 (op, expr) -> anf_c expr (fun expr -> k (Prim1 (op, expr)))
  | Prim2 (op, expr1, expr2) ->
      anf_imm expr1 (fun expr1 ->
          anf_imm expr2 (fun expr2 -> k (Prim2 (op, expr1, expr2))))
  | Let (id, bound_expr, body_expr) ->
      anf_c bound_expr (fun bound_expr ->
          Let (id, bound_expr, anf_c body_expr (fun body_expr -> k body_expr)))
  | If (cond_expr, true_expr, false_expr) ->
      let tmp = gensym "if" in
      Let
        ( tmp,
          If
            ( anf_c cond_expr (fun cond_expr -> cond_expr),
              anf_imm true_expr (fun true_expr -> true_expr),
              anf_imm false_expr (fun false_expr -> false_expr) ),
          k (Id tmp) )
  | Apply (f, args) ->
      let tmp = gensym "apply" in
      anf_imm_expr (Let (tmp, Apply (f, args), k (Id tmp))) []
  | Tuple el ->
    let tmp = gensym "tuple" in
    anf_imm_expr (Let (tmp, Tuple el, k (Id tmp))) []
  | Set (e, kval, v)  -> 
    let tmp = gensym "set" in
      anf_imm e (fun e -> 
        anf_imm kval (fun kval ->
          anf_imm v (fun v -> Let (tmp, Set (e, kval, v), k (Id tmp)))))
  | Lambda (args, body) -> 
    let tmp = gensym "lambda" in
      Let (tmp, Lambda (args, anf body) , k (Id tmp))
  | LamApply (f, args) -> 
      let tmp = gensym "lamapply" in
        anf_imm_expr (Let (tmp, LamApply (f, args), k (Id tmp))) []
  | LetRec (_) -> anf_imm_bindings expr [] k
and anf_imm_expr (expr : cexpr) (k : cexpr list) : cexpr =
  match expr with
  | Let (tmp, Apply (f, args), body_expr) -> (
      match args with
      | [] -> Let (tmp, Apply (f, List.rev k), body_expr)
      | h :: t ->
        anf_imm h (fun h ->
            anf_imm_expr (Let (tmp, Apply (f, t), body_expr)) (h :: k)))
  | Let (tmp, Tuple el, body_expr) -> (
    match el with
    | [] -> Let (tmp, Tuple (List.rev k), body_expr)
    | h :: t -> 
      anf_imm h (fun h ->
        anf_imm_expr (Let (tmp, Tuple t, body_expr)) (h :: k)))
  | Apply (f, args) -> (
      match args with
      | [] -> Apply (f, List.rev k)
      | h :: t -> anf_imm h (fun h -> anf_imm_expr (Apply (f, t)) (h :: k)))
  | Tuple el -> (
    match el with
    | [] -> Tuple (List.rev k)
    | h :: t -> anf_imm h (fun h -> anf_imm_expr (Tuple t) (h :: k)))
  | LamApply (f, args) -> (
    match args with
    | [] -> anf_imm f (fun f -> LamApply (f, (List.rev k)))
    | h :: t -> anf_imm h (fun h -> anf_imm_expr (LamApply (f, t)) (h :: k))
  )
  | Let (tmp, LamApply (f, args), body_expr) -> (
    match args with
    | [] -> Let (tmp, anf_imm f (fun f -> LamApply (f, (List.rev k))), body_expr)
    | h :: t -> anf_imm h (fun h -> anf_imm_expr (Let (tmp, LamApply (f, t), body_expr)) (h :: k))
  )
  | _ -> failwith "Woopsies"

and anf_bindings (expr : cexpr) (k: (string * string list * cexpr) list) =
  match expr with
  | LetRec (defs, body) -> (
    match defs with
    | [] -> LetRec ((List.rev k), anf body)
    | (id, args, lambda_body) :: t -> anf_bindings (LetRec (t, body)) ((id, args, anf lambda_body) :: k)
  )
  | _ -> failwith "Wooopsies :3"

and anf_c_bindings (expr : cexpr) (k : (string * string list * cexpr) list) (k2 : cexpr -> cexpr) =
  match expr with
  | LetRec (defs, body) -> (
    match defs with
    | [] -> LetRec ((List.rev k), anf_c body (fun body -> k2 body))
    | (id, args, lambda_body) :: t -> anf_c_bindings (LetRec (t, body)) ((id, args, anf lambda_body) :: k) k2
  )
  | _ -> failwith "Wooopsies :3"

and anf_imm_bindings (expr : cexpr) (k : (string * string list * cexpr) list) (k2 : cexpr -> cexpr) =
  match expr with
  | LetRec (defs, body) -> (
    match defs with
    | [] -> LetRec ((List.rev k), anf_imm body (fun body -> k2 body))
    | (id, args, lambda_body) :: t -> anf_imm_bindings (LetRec (t, body)) ((id, args, anf lambda_body) :: k) k2
  )
  | _ -> failwith "Wooopsies :3"