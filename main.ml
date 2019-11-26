open Core
open Opti
open Z3util
open Instruction

type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let predef = [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

let params_block_192 =
  let mk_add_1 = mk_bin_op "ADD_1" Instruction.enc_block_192 in
  Params.mk (predef @ [mk_add_1]) ~k:3 ~n:4

let params_block_ex1 = Params.mk predef ~k:3 ~n:2

let params_block_ex2 = Params.mk predef ~k:3 ~n:3

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
        let block_192 = Enc.enc_block_192 params_block_192  in
        let block_ex1 = Enc.enc_block_ex1 params_block_ex1 in
        let block_ex2 = Enc.enc_block_ex2 params_block_ex2 in
        set_options p_model p_smt;
        write_smt_and_map "block_192" block_192 params_block_192;
        write_smt_and_map "block_ex1" block_ex1 params_block_ex1;
        write_smt_and_map "block_ex2" block_ex2 params_block_ex2;
    ]
  |> Command.run ~version:"0.0"
