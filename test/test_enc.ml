(*   Copyright 2020 Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open OUnit2
open Syrup_backend
open User_params
open Instruction

let enc =
  [
    "Program with 0 length">:: (fun _ ->
        let ups = {
          n = 0;
          k = 3;
          ss = ["s_0"; "s_1"];
          src_ws = [Const "s_0";Const  "s_1"];
          tgt_ws = [Const "s_0"; Const "s_1"];
          curr_cst = 9;
          user_instrs = [];
          init_progr_len = 0;
        } in
        let params = Params.mk predef ups in
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["NOP"]
        (Print_trgt.show_disasm_mdl mdl params)
      );

    "Program pushing 146 on the stack">:: (fun _ ->
        let ups = {
          n = 2;
          k = 3;
          ss = [];
          src_ws = [];
          tgt_ws = [Val (Z.of_int 146)];
          curr_cst = 9;
          user_instrs = [];
          init_progr_len = 2;
        } in
        let params = Params.mk predef ups in
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["PUSH1 146"; "NOP"]
        (Print_trgt.show_disasm_mdl mdl params)
      );

    "Program duplicating top of the stack">:: (fun _ ->
        let ups = {
          n = 3;
          init_progr_len = 2;
          k = 3;
          ss = ["s_0"];
          src_ws = [Const "s_0"];
          tgt_ws = [Const "s_0"; Const "s_0"];
          curr_cst = 9;
          user_instrs = []
        } in
        let params = Params.mk predef ups in
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
        assert_equal
        ~cmp:[%eq: string list]
        ~printer:[%show: string list]
        ["DUP1"; "NOP" ]
        (Print_trgt.show_disasm_mdl mdl params)
      );

    "Program pushing CALLVALUE on the stack">:: (fun _ ->
        let ups = {
          n = 6;
          init_progr_len = 6;
          k = 5;
          ss = ["s(1)"; "s(2)"];
          src_ws = [Const "s(1)"];
          tgt_ws = [Const "s(2)"; Const "s(1)"];
          curr_cst = 9;
          user_instrs = [
            {
              id = "CALLVALUE_0";
              opcode = "34";
              disasm = "CALLVALUE";
              inpt_sk = [];
              outpt_sk = [Const "s(2)"];
              commutative = true;
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
        (Print_trgt.show_disasm_mdl mdl params)
      );

  ]

let suite = "suite" >::: enc

let () =
  run_test_tt_main suite
