open Core
open Z3util
open Consts
open Instruction
open Params
open Instruction_util

let pick_instr k params j =
  let t_j = mk_t j in
  let instrs = params.instrs in
  let instr iota = Params.enc_instr_name params iota in
  let open Z3Ops in
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (iota.effect k j))) &&
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j)))

let nop_propagate params n =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range 0 (n-1) in
  let nop = Z3util.num (Params.nop_enc_name params) in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop) ==> (t' j == nop)))

let enc_block k n params =
  let ns = List.range 0 n in
  let open Z3Ops in
  conj (List.map ns ~f:(pick_instr k params)) && nop_propagate params n

let enc_block_192 params =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let s_0 = mk_s 0 (* =^= 146 *) in
  let s_2 = Z3util.intconst ("sk_x") (* =^= input variable on stack *) in
  let s_1 = mk_s 1 (* =^= ADD_1 *) in
  let ss = [s_1; s_2]
  in
  let c_s =
    enc_sk_utlz_init k 1
  in
  let c_t =
    let xT_0 = mk_x 0 (n-1) in
    let open Z3Ops in
    (s_0 == num 146) && s_0 == xT_0
  in
  let
    target =
    let xT_1 = mk_x 1 (n-1) in
    let x_0_0 = mk_x 0 0 in
    let open Z3Ops in
    s_1 == xT_1 && (x_0_0 == s_2)
  in
  let open Z3Ops in
  foralls ss (target ==> c_s && c_t && (enc_block k n params))

let enc_block_ex1 params =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let s_0 = mk_s 0 (* =^= 146 *) in
  let ss = [] in
  let c_s = enc_sk_utlz_init k 0
  in
  let c_t =
    let open Z3Ops in
    (s_0 == num 146)
  in
  let target =
    let xT_0 = mk_x 0 (n-1) in
    let open Z3Ops in
    s_0 == xT_0
  in
  let open Z3Ops in
  foralls ss (target ==> c_s && c_t && (enc_block k n params))
