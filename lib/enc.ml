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

let force_instrs_in_tgt params =
  let instr iota = num (Params.instr_to_int params iota) in
  let open Z3Ops in
  let force_instr iota = disj (List.init params.n ~f:(fun j -> instr iota == mk_t j)) in
  conj (List.map params.instrs_in_tgt ~f:force_instr)

let force_instrs_in_tgt_at_most_once params =
  let instr iota = num (Params.instr_to_int params iota) in
  let open Z3Ops in
  let idxs_without j =
    List.range ~start:`inclusive ~stop:`exclusive 0 j @
    List.range ~start:`exclusive ~stop:`exclusive j params.n
  in
  let not_at_others iota j = conj (List.map (idxs_without j) ~f:(fun j' -> ~!(instr iota == mk_t j'))) in
  let max_one_slot iota = conj (List.init params.n ~f:(fun j -> (instr iota == mk_t j) ==> not_at_others iota j)) in
  conj (List.map params.instrs_in_tgt ~f:max_one_slot)

let enc_block ?rm_tgt_instr:(rm_tgt_instr = false) ?add_tgt_instr:(add_tgt_instr=false) params =
  let source_sk = sk_init params.k 0 params.src_ws in
  let target_sk = sk_init params.k params.n params.tgt_ws in
  let ns = List.range ~start:`inclusive ~stop:`exclusive 0 params.n in
  let open Z3Ops in
  source_sk && target_sk && for_all_vars params &&
  conj (List.map ns ~f:(pick_instr params))
  && nop_propagate params
  && bounds_push_args params
  && (if rm_tgt_instr then top else force_instrs_in_tgt params)
  && (if add_tgt_instr then force_instrs_in_tgt_at_most_once params else top)

let pick_from params instrs j =
  let enc_to_int iota = num (instr_to_int params iota) in
  let open Z3Ops in
  disj (List.map instrs ~f:(fun iota -> enc_to_int iota == mk_t j))

let enc_weight_at params j =
  List.fold (group_instr_by_gas params)
    ~init:((0, []), [])
    ~f:(fun ((prev_gas, all_prev_instrs), constrs) (curr_gas, instrs)  ->
        let weight = curr_gas - prev_gas in
        let constrs' = (pick_from params all_prev_instrs j, weight) :: constrs in
        let acc = (curr_gas, all_prev_instrs @ instrs) in
        (acc, constrs')
      )
  |> Tuple.T2.get2

let enc_weight params =
  List.init params.n ~f:(fun j -> enc_weight_at params j)
