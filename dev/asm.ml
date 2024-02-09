open Printf
open Parse

(* registers *)
type reg =
  (* callee saved *)
  | RBP
  | RSP
  | RBX
  | R12
  | R13
  | R14
  | R15
  (* caller saved *)
  | RAX
  | RCX
  | RDX
  | RSI
  | RDI
  | R8
  | R9
  | R10
  | R11

let fun_reg = [ RDI; RSI; RDX; RCX; R8; R9 ]

(* arguments for instructions *)
type arg = Const of int64 | Reg of reg | RegOffset of reg * int | Address of string

let reg_of_arg (a : arg) : reg =
  match a with Reg r -> r | RegOffset (r, _) -> r | _ -> raise (CTError "Compiler internal error")

let const_true = Const 0xFFFFFFFFFFFFFFFFL
let const_false = Const 0x7FFFFFFFFFFFFFFFL

(* generic type of instructions *)
type branch = JMP | JNE | JLE | JE | JZ | JNZ | JL | JGE
type binop = MOV | ADD | XOR | AND | CMP | TEST | SUB | OR | SAR | SHL | SHR | LEA
type unop = PUSH | POP | CALL

(* asm instructions *)
type instruction =
  | IRet
  | ILabel of string
  | ICall of string
  | IBinop of binop * arg * arg
  | IUnop of unop * arg
  | IBranch of branch * string
(* TO BE COMPLETED *)

let pp_branch b : string =
  match b with
  | JMP -> "jmp"
  | JNE -> "jne"
  | JLE -> "jle"
  | JGE -> "jge"
  | JL -> "jl"
  | JE -> "je"
  | JZ -> "jz"
  | JNZ -> "jnz"

let pp_binop b : string =
  match b with
  | LEA -> "lea"
  | MOV -> "mov"
  | ADD -> "add"
  | XOR -> "xor"
  | OR -> "or"
  | AND -> "and"
  | CMP -> "cmp"
  | TEST -> "test"
  | SUB -> "sub"
  | SAR -> "sar"
  | SHR -> "shr"
  | SHL -> "shl"


let pp_unop u : string = match u with PUSH -> "push" | POP -> "pop" | CALL -> "call"

let pp_reg reg : string =
  match reg with
  | RAX -> "RAX"
  | RBX -> "RBX"
  | RCX -> "RCX"
  | RDX -> "RDX"
  | RSP -> "RSP"
  | RBP -> "RBP"
  | RSI -> "RSI"
  | RDI -> "RDI"
  | R8 -> "R8"
  | R9 -> "R9"
  | R10 -> "R10"
  | R11 -> "R11"
  | R12 -> "R12"
  | R13 -> "R13"
  | R14 -> "R14"
  | R15 -> "R15"

let pp_arg arg : string =
  match arg with
  | Const n -> sprintf "%#Lx" n
  | Reg r -> pp_reg r
  | RegOffset (r, n) ->
      if n >= 0 then sprintf "[%s +%d]" (pp_reg r) (8 * n)
      else sprintf "[%s %d]" (pp_reg r) (8 * n)
  | Address s -> sprintf "[rel %s]" s

let pp_instr instr : string =
  match instr with
  | IRet -> "  ret"
  | ILabel s -> sprintf "%s:" (String.map (fun c -> if (c == '-') then '_' else c) s)
  | ICall a -> sprintf "  call %s" (String.map (fun c -> if (c == '-') then '_' else c) a)
  | IBranch (b, s) -> sprintf "  %s %s" (pp_branch b) (String.map (fun c -> if (c == '-') then '_' else c) s)
  | IBinop (b, a1, a2) ->
      sprintf "  %s %s, %s" (pp_binop b) (pp_arg a1) (pp_arg a2)
  | IUnop (u, a) -> sprintf "  %s %s" (pp_unop u) (pp_arg a)

let pp_instrs (instrs : instruction list) : string =
  List.fold_left (fun res i -> res ^ "\n" ^ pp_instr i) "" instrs
