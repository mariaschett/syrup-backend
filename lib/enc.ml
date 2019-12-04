open Core
open Z3util
open Consts
open Instruction
open Params
open Sk_util

let pick_instr params j =
  let t_j = mk_t j in
  let instrs = params.instrs in
  let instr iota = num (Params.instr_to_int params iota) in
  let open Z3Ops in
  conj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (iota.effect params.k j))) &&
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j)))

let nop_propagate params =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range ~start:`inclusive ~stop:`exclusive 0 (params.n - 1) in
  let nop = find_instr params ~id:"NOP" in
  let nop_to_int = Z3util.num (instr_to_int params nop) in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop_to_int) ==> (t' j == nop_to_int)))

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

let weight params j =
  let gas_constr = Z3.Symbol.mk_string !ctxt "gas" in
  let nop = find_instr params ~id:"NOP" in
  let nop_to_int = Z3util.num (instr_to_int params nop) in
  let open Z3Ops in
  Z3.Optimize.add_soft !octxt (~! (nop_to_int == mk_t j)) "2" gas_constr
