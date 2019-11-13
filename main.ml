open Core
open Opti
open Z3util

type output_options =
  { pmodel : bool
  ; psmt : bool
  }

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
        let block_192 = Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" [] Enc.enc_block_192 in
        let block_ex1 = Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" [] Enc.enc_block_ex1 in
        set_options p_model p_smt;
        print_string block_192;
        Out_channel.write_all "examples/block_192.smt" ~data:block_192;
        Out_channel.write_all "examples/block_ex1.smt" ~data:(block_ex1^"(get-model)");
    ]
  |> Command.run ~version:"0.0"
