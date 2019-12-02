open OUnit2
open Opti
open Instruction
open Inpt

let predef = [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

let ui =
  let add_1 = {
    id = "ADD_1";
    opcode = "00";
    disasm = "ADD";
    input_stack = [Const "s_0"; Val 1];
    output_stack = [Const "s_1"]
  }
  in
  { n = 4;
    k = 3;
    ss = ["s_0"; "s_1"];
    src_ws = [Const "s_0"];
    tgt_ws = [Val 146; Const "s_1"];
    user_instrs = [add_1]
  }

let inpt = [

  "Set n correctly">:: (fun _ ->
      let p = to_params predef ui in
      assert_equal
        ~cmp:[%eq: int]
        ~printer:[%show: int]
        ui.n
        p.n
    );
  ]

let suite = "suite" >::: inpt

let () =
  run_test_tt_main suite
