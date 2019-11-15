open Core
open Opti
open Z3util

type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let show_smt ex =
  let smt = Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" [] ex in
  (* hack get model *)
  smt ^ "(get-model)"

let write_smt_and_map fn ex params =
  Out_channel.write_all ("examples/"^fn^".smt") ~data:ex;
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
        let params = Params.mk Instruction.all in
        let block_192 = show_smt (Enc.enc_block_192 params) in
        let block_ex1 = show_smt (Enc.enc_block_ex1 params) in
        set_options p_model p_smt;
        write_smt_and_map "block_192" block_192 params;
        write_smt_and_map "block_ex1" block_ex1 params
    ]
  |> Command.run ~version:"0.0"
