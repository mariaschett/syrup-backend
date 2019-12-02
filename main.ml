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

let add_1 = {
  id = "ADD_1";
  opcode = "00";
  disasm = "ADD";
  input_stack = [Const "s_0"; Val 1];
  output_stack = [Const "s_1"]
}

let add_1_rev = {
  id = "ADD_1";
  opcode = "00";
  disasm = "ADD";
  input_stack = [Val 1; Const "s_0"];
  output_stack = [Const "s_1"]
}

let user_params_block_192 ui =
  { n = 4;
    k = 3;
    ss = ["s_0"; "s_1"];
    src_ws = [Const "s_0"];
    tgt_ws = [Val 146; Const "s_1"];
    user_instrs = ui
  }

let user_params_ex_1 =
  { n = 2;
    k = 3;
    ss = [];
    src_ws = [];
    tgt_ws = [Val 146];
    user_instrs = [];
  }

let user_params_ex_2 =
  { n = 3;
    k = 3;
    ss = ["s_0"];
    src_ws = [Const "s_0"];
    tgt_ws = [Const "s_0"; Const "s_0"];
    user_instrs = [];
  }

let params p = Params.mk (predef @ (get_user_instrs p))
    ~k:(get_k p) ~n:4 ~src_ws:(get_src_ws p) ~tgt_ws:(get_tgt_ws p) ~ss:(get_ss p)

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
          [("block_192", params (user_params_block_192 [add_1]));
           ("block_192_rev", params (user_params_block_192 [add_1_rev]));
           ("block_ex1", params user_params_ex_1);
           ("block_ex2", params user_params_ex_2)] in
        set_options p_model p_smt;
        List.fold all ~init:() ~f:(fun _ (name, params) ->
            let enc = Enc.enc_block params in
            write_smt_and_map name enc params)

    ]
  |> Command.run ~version:"0.0"
