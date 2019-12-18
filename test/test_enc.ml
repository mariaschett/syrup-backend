open Core
open OUnit2
open Opti
open Z3util
open User_params
open Instruction

let get_max_model_exn params =
  Z3.Optimize.push !octxt;
  let enc = Enc.enc_block params in
  let _ = Enc.enc_weight params in
  let _ = Z3.Optimize.add !octxt [enc] in
  let _ = Z3.Optimize.check !octxt in
  let mdl = Option.value_exn (Z3.Optimize.get_model !octxt)
  in
  Z3.Optimize.pop !octxt;
  mdl

let enc =
  [
    "Program pushing 146 on the stack">:: (fun _ ->
        let ups = {
          n = 2;
          k = 3;
          ss = [];
          src_ws = [];
          tgt_ws = [Val 146];
          user_instrs = []
        } in
        let params = Params.mk predef ups in
        let mdl = get_max_model_exn params in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["PUSH1 146"; "NOP"]
        (Outpt.show_disasm mdl params)
      );

    "Program duplicating top of the stack">:: (fun _ ->
        let ups = {
          n = 3;
          k = 3;
          ss = ["s_0"];
          src_ws = [Const "s_0"];
          tgt_ws = [Const "s_0"; Const "s_0"];
          user_instrs = []
        } in
        let params = Params.mk predef ups in
        let mdl = get_max_model_exn params in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["DUP"; "NOP"; "NOP"]
        (Outpt.show_disasm mdl params)
      );

    "Program pushing CALLVALUE on the stack">:: (fun _ ->
        let ups = {
          n = 6;
          k = 5;
          ss = ["s(1)"; "s(2)"];
          src_ws = [Const "s(1)"];
          tgt_ws = [Const "s(1)"; Const "s(2)";];
          user_instrs = [
            {
              id = "CALLVALUE_0";
              opcode = "34";
              disasm = "CALLVALUE";
              inpt_sk = [];
              outpt_sk = [Const "s(2)"];
              gas = 2;}
          ];
        }
        in
        let params = Params.mk predef ups in
        let mdl = get_max_model_exn params in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["CALLVALUE_0"; "SWAP"; "NOP"; "NOP"; "NOP"; "NOP"]
        (Outpt.show_disasm mdl params)
      );

  ]

let suite = "suite" >::: enc

let () =
  run_test_tt_main suite
