open Core
open Z3util
open Consts
open Instruction
open Params
open Instruction_util

let pick_instr k params enc_userdef j =
  let t_j = mk_t j in
  let instrs = params.instrs in
  let instr iota = Params.enc_instr_name params iota in
  let open Z3Ops in
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j) ==> (effect k enc_userdef iota j))) &&
  disj (List.map instrs ~f:(fun iota -> (instr iota == t_j)))

let nop_propagate params n =
  let t j = mk_t j in
  let t' j = mk_t (j+1) in
  let ns = List.range 0 (n-1) in
  let nop = Params.enc_instr_name params (PREDEF NOP) in
  let open Z3Ops in
  conj (List.map ns ~f:(fun j -> (t j == nop) ==> (t' j == nop)))

let enc_block k n params enc_userdef =
  let ns = List.range 0 n in
  let open Z3Ops in
  conj (List.map ns ~f:(pick_instr k params enc_userdef)) && nop_propagate params n

let enc_block_192 params =
  (* max elements ever on stack *)
  let k = 3 in
  (* max target program simze *)
  let n = 2 in
  let s_0 = mk_s 0 (* =^= 146 *) in
  let s_2 = Z3util.intconst ("sk_x") (* =^= input variable on stack *) in
  let s_1 = mk_s 1 (* =^= f_ADD(sk_x, 1) *) in
  let ss = [s_1; s_2] in

  (* fixed to example block 192 *)
  let enc_instr_block_192  j =
    let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
    let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
    let x_1 = mk_x 1 j in
    let diff = diff (USERDEF Block_192) in
    let alpha = alpha (USERDEF Block_192) in
    let open Z3Ops in
    u_0 && u_1 ==> (
        ((x_0 == s_2) && (x_1 == (num 1))) ==> (x'_0 == s_1) &&
        enc_prsv k j diff alpha && enc_sk_utlz k j diff)
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
  foralls ss (target ==> c_s && c_t && (enc_block k n params enc_instr_block_192))

let enc_block_ex1 params =
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
    let open Z3Ops in
    (s_0 == num 146)
  in
  let target =
    let xT_0 = mk_x 0 (n-1) in
    let open Z3Ops in
    s_0 == xT_0
  in
  let open Z3Ops in
  foralls ss (target ==> c_s && c_t && (enc_block k n params enc_instr_block_ex1))
