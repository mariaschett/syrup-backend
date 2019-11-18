open Core
open Opti
open Z3util
open Instruction
open Consts
open Instruction_util

type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let predef = [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

(* fixed to example block 192 *)
let enc_block_192 diff alpha k j =
  let s_2 = Z3util.intconst ("sk_x") (* =^= input variable on stack *) in
  let s_1 = mk_s 1 (* =^= f_ADD(sk_x, 1) *) in
  let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
  let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
  let x_1 = mk_x 1 j in
  let open Z3Ops in
  u_0 && u_1 && (((x_0 == s_2) && (x_1 == (num 1))) ==> (x'_0 == s_1)) &&
      enc_prsv k j diff alpha && enc_sk_utlz k j diff

let mk_block_192 =
  let name = "ADD_1" in
  let alpha = 1 and delta = 2 in
  let diff = alpha - delta in
  Instruction.mk name alpha delta (enc_block_192 diff alpha)

let show_smt ex =
  let smt = Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" [] ex in
  (* hack get model *)
  smt ^ "(get-model)"

let write_smt_and_map fn ex params =
  let ex' = show_smt ex in
  Out_channel.write_all ("examples/"^fn^".smt") ~data:ex';
  Out_channel.write_all ("examples/"^fn^".map") ~data:(Params.show_map params)

let outputcfg =
  ref {pmodel = false; psmt = false;}

let set_options pm psmt =
  outputcfg := {pmodel = pm; psmt = psmt;}

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"opti: an optimizer"
    [%map_open
      let p_model = flag "print-model" no_arg
          ~doc:"print model found by solver"
      and p_smt = flag "print-smt" no_arg
          ~doc:"print constraint given to solver in SMT-LIB format"
      in
      fun () ->
        let params_block_192 = Params.mk (predef @ [mk_block_192]) in
        let params_block_ex1 = Params.mk predef in
        let block_192 = Enc.enc_block_192 params_block_192 in
        let block_ex1 = Enc.enc_block_ex1 params_block_ex1 in
        set_options p_model p_smt;
        write_smt_and_map "block_192" block_192 params_block_192;
        write_smt_and_map "block_ex1" block_ex1 params_block_ex1;
    ]
  |> Command.run ~version:"0.0"
