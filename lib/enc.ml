open Core
open Z3util
open Consts
open Instruction

(* stack utilization *)

let enc_sk_utlz_init k l =
  let u i = mk_u i 0 in
  let is_utlzd i =  if i < l then top else btm in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u i == is_utlzd i))

let enc_sk_utlz_shft k j diff =
  let u' i = mk_u' i j in
  let u i = mk_u i j in
  let shft i =
    if (diff < 0)
    then
      (if i < abs(diff) then top else u (i+diff))
    else
      (if i > k - diff then btm else u (i+diff))
  in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u' i == shft i))

(* assumes u_k-1_j is not utilized *)
let enc_sk_utlz_add k j diff = enc_sk_utlz_shft k j (-diff)
let enc_sk_utlz_unchanged k j = enc_sk_utlz_shft k j 0

(* no effect if u_0_j is not utilized *)
let enc_sk_utlz_rm k j diff = enc_sk_utlz_shft k j diff

let enc_sk_utlz k j iota = enc_sk_utlz_shft k j (diff iota)

(* preserve *)

let enc_prsv_from_diff diff k l j =
  let x i = mk_x i j and x' i = mk_x' (i-diff) j in
  let u i = mk_u i j in
  let ks = List.range l k in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> u i ==> (x' i == x i)))

let enc_prsv k j iota =
  enc_prsv_from_diff (diff iota) k (alpha iota) j

(* effect *)

let enc_push k j =
  let x'_0 = mk_x' 0 j in
  let u_k = mk_u (k-1) j in
  let a = mk_a j in
  let open Z3Ops in
  ~! u_k &&
  (x'_0 == a && enc_prsv k j (PREDEF PUSH) && enc_sk_utlz k j (PREDEF PUSH))

let enc_pop k j =
  let u_0 = mk_u 0 j in
  let open Z3Ops in
  u_0 && (enc_prsv k j (PREDEF POP) && enc_sk_utlz k j (PREDEF POP))

let enc_swap k j =
  let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
  let x_1 = mk_x 1 j and x'_1 = mk_x' 1 j in
  let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
  let open Z3Ops in
  u_0 && u_1 &&
  ((x'_0 == x_1) && (x'_1 == x_0)) && enc_prsv k j (PREDEF SWAP) && enc_sk_utlz k j (PREDEF SWAP)

let enc_dup k j =
  let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
  let x'_1 = mk_x' 1 j in
  let u_0 = mk_u 0 j and u_l = mk_u (k-1) j in
  let open Z3Ops in
  u_0 && ~! u_l &&
  ((x'_0 == x_0) && (x'_1 == x_0) && enc_prsv k j (PREDEF DUP) && enc_sk_utlz k j (PREDEF DUP))

let enc_nop k j =
  let open Z3Ops in
  enc_prsv k j (PREDEF NOP) && enc_sk_utlz k j (PREDEF NOP)

let effect k enc_userdef iota j =
  match iota with
  | PREDEF PUSH -> enc_push k j
  | PREDEF POP -> enc_pop k j
  | PREDEF SWAP -> enc_swap k j
  | PREDEF DUP -> enc_dup k j
  | PREDEF NOP -> enc_nop k j
  | USERDEF Block_192 -> enc_userdef j


let pick_instr k enc_userdef j =
  let t_j = mk_t j in
  let instr iota = Instruction.enc iota in
  let instrs = Instruction.all in
  let open Z3Ops in
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (effect k enc_userdef iota j))) &&
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j)))

let nop_propagate n =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range 0 (n-1) in
  let nop = Instruction.enc (PREDEF NOP) in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop) ==> (t' j == nop)))

let enc_block k n c_s c_t ss enc_userdef =
  let ns = List.range 0 n in
  let open Z3Ops in
  foralls ss (c_s && c_t && conj (List.map ns ~f:(pick_instr k enc_userdef)) && nop_propagate n)

let enc_block_192 =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let s_0 = mk_s 0 (* =^= 146 *) in
  let s_2 = Z3util.intconst ("sk_x") (* =^= input variable on stack *) in
  let s_1 = mk_s 1 (* =^= f_ADD(sk_x, 1) *) in
  let ss = [s_1; s_2] in

  (* fixed to example block 192 *)
  let enc_instr_block_192 j =
    let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
    let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
    let x_1 = mk_x 1 j in
    let open Z3Ops in
    u_0 && u_1 ==> (
        ((x_0 == s_2) && (x_1 == (num 1))) ==> (x'_0 == s_1) &&
        enc_prsv k j (USERDEF Block_192) && enc_sk_utlz_rm k j 1)
  in
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
  enc_block k n c_s c_t ss enc_instr_block_192


let enc_block_ex1 =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let s_0 = mk_s 0 (* =^= 146 *) in
  let ss = [] in
  (* fixed to example block 192 *)
  let enc_instr_block_ex1 _ = Z3util.btm
  in
  let c_s = enc_sk_utlz_init k 0
  in
  let c_t =
    let xT_0 = mk_x 0 (n-1) in
    let open Z3Ops in
    (s_0 == num 146) && conj [s_0 == xT_0]
  in
  enc_block k n c_s c_t ss enc_instr_block_ex1
