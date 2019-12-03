open Core
open Opti
open Z3util
open Instruction
open Inpt

type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let predef = [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

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
        let all =
          [("block_192", read_inpt "input/block_192.json");
           ("block_192_rev", read_inpt "input/block_192_rev.json");
           ("block_ex1", read_inpt "input/block_ex1.json");
           ("block_ex2", read_inpt "input/block_ex2.json")] in
        set_options p_model p_smt;
        List.fold all ~init:() ~f:(fun _ (name, up) ->
            let params = to_params predef up in
            let enc = Enc.enc_block params in
            write_smt_and_map name enc params)

    ]
  |> Command.run ~version:"0.0"
