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

let for_all_vars params =
  let fresh_num i = bignum (Z.add params.max_wsz (Z.of_int i)) in
  let open Z3Ops in
  conj (List.mapi params.ss ~f:(fun i s -> s == fresh_num i))

let enc_block params =
  let source_sk = sk_init params.k 0 params.src_ws in
  let target_sk = sk_init params.k params.n params.tgt_ws in
  let ns = List.range ~start:`inclusive ~stop:`exclusive 0 params.n in
  let open Z3Ops in
  source_sk && target_sk && for_all_vars params &&
  conj (List.map ns ~f:(pick_instr params))
  && nop_propagate params
  && bounds_push_args params
