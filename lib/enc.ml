open Core
open Z3util
open Consts
open Instruction
open Params
open Sk_util

let pick_instr params j =
  let t_j = mk_t j in
  let instrs = params.instrs in
  let instr iota = Params.enc_instr_name params iota in
  let open Z3Ops in
  conj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (iota.effect params.k j))) &&
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j)))

let nop_propagate params =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range ~start:`inclusive ~stop:`exclusive 0 (params.n - 1) in
  let nop = Z3util.num (Params.nop_enc_name params) in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop) ==> (t' j == nop)))

let bounds_push_args params =
  let a j = mk_a j in
  let ns = List.range ~start:`inclusive ~stop:`exclusive 0 params.n in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> num 0 <= a j && a j < bignum params.max_wsz))

let enc_block params =
  let ns = List.range ~start:`inclusive ~stop:`exclusive 0 params.n in
  let open Z3Ops in
  conj (List.map ns ~f:(pick_instr params))
  && nop_propagate params
  && bounds_push_args params

let enc_block_192 params =
  let s_1 = mk_s 1 (* =^= ADD_1 *) in
  let s_2 = Z3util.intconst ("sk_x") (* =^= input variable on stack *) in
  let source_sk = sk_init params.k 0 [s_2] in
  let target_sk = sk_init params.k (params.n-1) [s_1; num 146] in
  let fresh_num i = bignum (Z.add params.max_wsz (Z.of_int i)) in
  let all_vars =
    conj (List.mapi params.ss ~f:(fun i s -> s <==> fresh_num i)) in
  let open Z3Ops in
  source_sk && target_sk && enc_block params && all_vars

let enc_block_ex1 params =
  let source_sk = sk_init params.k 0 [] in
  let target_sk = sk_init params.k (params.n-1) [num 146] in
  let open Z3Ops in
  source_sk && target_sk && enc_block params

let enc_block_ex2 params =
  let s_0 = Consts.mk_s 0 in
  let sk_x = Z3util.intconst ("sk_x") in
  let source_sk = sk_init params.k 0 [s_0] in
  let target_sk = sk_init params.k (params.n-1) [s_0; s_0] in
  let cstrs = let open Z3Ops in s_0 == sk_x in
  let fresh_num i = bignum (Z.add params.max_wsz (Z.of_int i)) in
  let all_vars =
    conj (List.mapi params.ss ~f:(fun i s -> s <==> fresh_num i)) in
  let open Z3Ops in
  source_sk && target_sk && cstrs && enc_block params && all_vars
