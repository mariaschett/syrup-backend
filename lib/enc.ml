open Core
open Z3util

module Instruction = struct
  type t =
      SWAP
    | PUSH
    | ADD
    | POP
    | DUP
    | NOP
  [@@deriving show {with_path = false}, enumerate]
end

(* stack utilization *)
let mk_u i j = Z3util.boolconst ("u" ^ [%show: int] i ^ "_" ^ [%show: int] j)

(* word *)
let mk_x i j = Z3util.intconst ("x_" ^ [%show: int] i ^ "_" ^ [%show: int] j)
let mk_a j = Z3util.intconst ("a_" ^ [%show: int] j)
let mk_s j = Z3util.intconst ("s_" ^ [%show: int] j)

(* instruction *)
let mk_instr n = Z3util.intconst ("instr_" ^ [%show: Instruction.t] n)
let mk_t j = Z3util.intconst ("t_" ^ [%show: int] j)

(* current elements on the stack *)
let s_0 = mk_s 0
let s_1 = mk_s 1
let s_2 = Z3util.intconst ("sk_x")
let ss = [s_1; s_2]

let eqs=
  let open Z3Ops in
  (s_0 == num 146)

let enc_add j =
  let x_0 = mk_x 0 j and x'_0 = mk_x 0 (j+1) in
  let x_1 = mk_x 1 j in
  let b_0 = mk_u 0 j and b_1 = mk_u 1 j in
  let open Z3Ops in
  (* fixed to example *)
  (b_0 && b_1) ==>
  (((x_0 == s_2) && (x_1 == (num 1))) ==> (x'_0 == s_1))

(* preserve *)

let enc_pres_from_delta delta k l j =
  let x i = mk_x i j and x' i = mk_x (i+delta) (j+1) in
  (* TODO check range! *)
  let ks = List.range l (k - delta) in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> x' i == x i))

let enc_pres_move_up_from = enc_pres_from_delta 1
let enc_pres_all_from = enc_pres_from_delta 0
let enc_pres_move_down = enc_pres_from_delta (-1)

(* stack counter *)

let enc_sc_init k l =
  let b_x i = mk_u i 0 in
  let ks = List.range l k in
  let ls = List.range 0 l in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> b_x i == btm)) &&
  conj (List.map ls ~f:(fun i -> b_x i == top))

let enc_sc_unchanged k j =
  let b_x i = mk_u i j and b'_x i = mk_u i (j+1) in
  let ks = List.range 0 k in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> b_x i == b'_x i))

let enc_sc_add_one k j =
  let ks = List.range 0 (k-1) in
  let b_x i = mk_u i j in
  let b'_x' i = mk_u (i+1) (j+1) in
  let b'_btm = mk_u 0 (j+1) in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> b'_x' i == b_x i)) && (b'_btm == top)

let enc_sc_rm_one k j =
  let ks = List.range 1 k in
  let b_x i = mk_u i j in
  let b'_x' i = mk_u (i-1) (j+1) in
  let b'_fin = b'_x' (k-1) in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> b'_x' i == b_x i)) && (b'_fin == btm)

(* effect *)

let enc_swap j =
  let x_0 = mk_x 0 j and x'_0 = mk_x 0 (j+1) in
  let x_1 = mk_x 1 j and x'_1 = mk_x 1 (j+1) in
  let b_0 = mk_u 0 j and b_1 = mk_u 1 j in
  let open Z3Ops in
  (b_0 && b_1) ==>
  ((x'_0 == x_1) && (x'_1 == x_0))

let enc_dup j =
  let x_0 = mk_x 0 j and x'_0 = mk_x 0 (j+1) in
  let x'_1 = mk_x 1 (j+1) in
  let open Z3Ops in
  (x'_0 == x_0) && (x'_1 == x_0)

let enc_push j =
  let x'_0 = mk_x 0 (j+1) in
  let a = mk_a j in
  let open Z3Ops in
  (x'_0 == a)

let effect k iota j =
  let open Z3Ops in
  match iota with
  | Instruction.SWAP ->
    enc_swap j && enc_pres_all_from k 2 j && enc_sc_unchanged k j
  | Instruction.DUP ->
    enc_dup j && enc_pres_move_up_from k 1 j && enc_sc_add_one k j
  | Instruction.POP ->
    enc_pres_move_down k 1 j && enc_sc_rm_one k j
  | Instruction.NOP ->
    enc_pres_all_from k 0 j && enc_sc_unchanged k j
  | Instruction.ADD ->
    enc_add j && enc_pres_move_up_from k 2 j && enc_sc_rm_one k j
  | Instruction.PUSH ->
    enc_push j && enc_pres_move_up_from k 0 j && enc_sc_add_one k j

let pick_instr k j =
  let t_j = mk_t j in
  let instr iota = mk_instr iota in
  let instrs = Instruction.all in
  let open Z3Ops in
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (effect k iota j)))

let pick_target k n =
  let ns = List.range 0 n in
  conj (List.map ns ~f:(pick_instr k))

let nop_propagate n =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range 0 n in
  let nop = mk_instr Instruction.NOP in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop) ==> (t' j == nop)))

let enc_block_192 =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let xT_0 = mk_x 0 (n-1) in
  let xT_1 = mk_x 1 (n-1) in
  let open Z3Ops in
  let trgt_sk = conj [ s_0 == xT_0 ; s_1 == xT_1] in
  (foralls ss (trgt_sk && pick_target k n && nop_propagate n)) && eqs
  && enc_sc_init k 2
