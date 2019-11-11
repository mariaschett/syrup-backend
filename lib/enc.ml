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

(* stack utilization at stack index i after j instructions *)
let mk_u i j = Z3util.boolconst ("u_" ^ [%show: int] i ^ "_" ^ [%show: int] j)

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
  let open Z3Ops in
  (* fixed to example *)
  ((x_0 == s_2) && (x_1 == (num 1))) ==> (x'_0 == s_1)

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

(* stack utilization *)

let enc_sk_utilz_init k l =
  let u i = mk_u i 0 in
  let is_utilzd i =  if i < l then top else btm in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u i == is_utilzd i))

let enc_sk_utilz_shft k j shft =
  let u' i = mk_u i (j+1) in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u' i == shft i))

(* assumes u_k-1_j is not utilized *)
let enc_sk_utilz_add k j delta =
  let u i = mk_u i j in
  let shft i = if i < delta then top else u (i-delta) in
  enc_sk_utilz_shft k j shft

(* no effect if u_0_j is not utilized *)
let enc_sk_utilz_rm k j delta =
  let u i = mk_u i j in
  let shft i = if i > k - delta then btm else u (i+delta) in
  enc_sk_utilz_shft k j shft

let enc_sk_utilz_unchanged k j = enc_sk_utilz_add k j 0

(* effect *)

let enc_swap j =
  let x_0 = mk_x 0 j and x'_0 = mk_x 0 (j+1) in
  let x_1 = mk_x 1 j and x'_1 = mk_x 1 (j+1) in
  let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
  let open Z3Ops in
  (u_0 && u_1) ==>
  ((x'_0 == x_1) && (x'_1 == x_0))

let enc_dup j =
  let x_0 = mk_x 0 j and x'_0 = mk_x 0 (j+1) in
  let x'_1 = mk_x 1 (j+1) in
  let open Z3Ops in
  (x'_0 == x_0) && (x'_1 == x_0)

let enc_push j =
  let x'_0 = mk_x 0 (j+1) in
  let a = mk_a (j+1) in
  let open Z3Ops in
  (x'_0 == a)

let effect k iota j =
  let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
  let u_l = mk_u (k-1) j in
  let open Z3Ops in
  match iota with
  | Instruction.SWAP ->
    u_0 && u_1 ==>
    (enc_swap j && enc_pres_all_from k 2 j && enc_sk_utilz_unchanged k j)
  | Instruction.DUP ->
    u_0 && ~! u_l ==>
    (enc_dup j && enc_pres_move_up_from k 1 j && enc_sk_utilz_add k j 1)
  | Instruction.POP ->
    u_0 ==>
    (enc_pres_move_down k 1 j && enc_sk_utilz_rm k j 1)
  | Instruction.NOP ->
    enc_pres_all_from k 0 j && enc_sk_utilz_unchanged k j
  | Instruction.ADD ->
    u_0 && u_1 ==>
    (enc_add j && enc_pres_move_up_from k 2 j && enc_sk_utilz_rm k j 1)
  | Instruction.PUSH ->
    ~! u_l ==>
    (enc_push j && enc_pres_move_up_from k 0 j && enc_sk_utilz_add k j 1)

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
  let trgt_sk = conj [s_0 == xT_0 ; s_1 == xT_1] in
  (foralls ss (trgt_sk && pick_target k n && nop_propagate n)) && eqs
  && enc_sk_utilz_init k 2
