open Core
open Z3util open Instruction

(* program counter *)
type pc = int [@@deriving show {with_path = false}]

(* stack index *)
type si = int [@@deriving show {with_path = false}]

(* stack utilization u at stack index i after j instructions *)
let mk_u (i : si) (j : pc) =
  Z3util.boolconst ("u_" ^ [%show: pc] i ^ "_" ^ [%show: si] j)

(* words on stack are modeled as integer *)
(* word x at stack index i after executing j instructions *)
let mk_x (i : si) (j : pc) =
  Z3util.intconst ("x_" ^ [%show: pc] i ^ "_" ^ [%show: si] j)
(* argument a of instruction after j instructions *)
let mk_a (j : pc) = Z3util.intconst ("a_" ^ [%show: pc] j)

(* instructions are modeled as integers *)
(* template t to assign instructions *)
let mk_t (j : pc) = Z3util.intconst ("t_" ^ [%show: pc] j)

(* words on the final stack *)
let mk_s (j : pc) = Z3util.intconst ("s_" ^ [%show: int] j)

(* fixed to example block 192 *)
let s_0 = mk_s 0 (* =^= 146 *)
let s_2 = Z3util.intconst ("sk_x") (* =^= input variable on stack *)
let s_1 = mk_s 1 (* =^= f_ADD(sk_x, 1) *)
let ss = [s_1; s_2]

(* fixed to example block 192 *)
let enc_block_192 j =
  let x_0 = mk_x 0 j and x'_0 = mk_x 0 (j+1) in
  let x_1 = mk_x 1 j in
  let open Z3Ops in
  ((x_0 == s_2) && (x_1 == (num 1))) ==> (x'_0 == s_1)

(* stack utilization *)

let enc_sk_utlz_init k l =
  let u i = mk_u i 0 in
  let is_utlzd i =  if i < l then top else btm in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u i == is_utlzd i))

let enc_sk_utlz_shft k j shft =
  let u' i = mk_u i (j+1) in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u' i == shft i))

(* assumes u_k-1_j is not utilized *)
let enc_sk_utlz_add k j delta =
  let u i = mk_u i j in
  let shft i = if i < delta then top else u (i-delta) in
  enc_sk_utlz_shft k j shft

(* no effect if u_0_j is not utilized *)
let enc_sk_utlz_rm k j delta =
  let u i = mk_u i j in
  let shft i = if i > k - delta then btm else u (i+delta) in
  enc_sk_utlz_shft k j shft

let enc_sk_utlz_unchanged k j = enc_sk_utlz_add k j 0

(* preserve *)

let enc_prsv_from_diff diff k l j =
  let x i = mk_x i j and x' i = mk_x (i-diff) (j+1) in
  let u i = mk_u i j in
  let ks = List.range l k in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> u i ==> (x' i == x i)))

let enc_prsv k j iota =
  enc_prsv_from_diff (diff iota) k (alpha iota) j

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
  | SWAP ->
    u_0 && u_1 ==>
    (enc_swap j && enc_prsv k j iota && enc_sk_utlz_unchanged k j)
  | DUP ->
    u_0 && ~! u_l ==>
    (enc_dup j && enc_prsv k j iota && enc_sk_utlz_add k j 1)
  | POP ->
    u_0 ==>
    (enc_prsv k j iota && enc_sk_utlz_rm k j 1)
  | NOP ->
    enc_prsv k j iota && enc_sk_utlz_unchanged k j
  | USERDEF Block_192 ->
    u_0 && u_1 ==>
    (enc_block_192 j && enc_prsv k j iota && enc_sk_utlz_rm k j 1)
  | PUSH ->
    ~! u_l ==>
    (enc_push j && enc_prsv k j iota && enc_sk_utlz_add k j 1)

let pick_instr k j =
  let t_j = mk_t j in
  let instr iota = Instruction.enc iota in
  let instrs = Instruction.all in
  let open Z3Ops in
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (effect k iota j)))

let nop_propagate n =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range 0 (n-1) in
  let nop = Instruction.enc NOP in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop) ==> (t' j == nop)))

let enc_block_192 =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let ns = List.range 0 n in
  let c_s =
    let x_0_0 = mk_x 0 0 in
    let open Z3Ops in
    (x_0_0 == s_2) && enc_sk_utlz_init k 1
  in
  let c_t =
    let xT_0 = mk_x 0 (n-1) in
    let xT_1 = mk_x 1 (n-1) in
    let open Z3Ops in
    (s_0 == num 146) && conj [s_0 == xT_0 ; s_1 == xT_1]
  in
  let open Z3Ops in
  foralls ss (c_s && c_t && conj (List.map ns ~f:(pick_instr k)) && nop_propagate n)
