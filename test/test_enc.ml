open OUnit2
open Opti
open User_params
open Instruction

let enc =
  [
    "Program pushing 146 on the stack">:: (fun _ ->
        let ups = {
          n = 2;
          k = 3;
          ss = [];
          src_ws = [];
          tgt_ws = [Val (Z.of_int 146)];
          user_instrs = []
        } in
        let params = Params.mk predef ups in
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
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
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["DUP1"; "NOP"; "NOP"]
        (Outpt.show_disasm mdl params)
      );

    "Program pushing CALLVALUE on the stack">:: (fun _ ->
        let ups = {
          n = 6;
          k = 5;
          ss = ["s(1)"; "s(2)"];
          src_ws = [Const "s(1)"];
          tgt_ws = [Const "s(2)"; Const "s(1)"];
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
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["CALLVALUE"; "NOP"; "NOP"; "NOP"; "NOP"; "NOP"]
        (Outpt.show_disasm mdl params)
      );

  ]

let suite = "suite" >::: enc

let () =
  run_test_tt_main suite
