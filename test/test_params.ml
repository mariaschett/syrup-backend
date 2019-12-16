open Core
open OUnit2
open Opti
open User_params

let ups_0 = {
  n = 4;
  k = 3;
  ss = ["s_0";];
  src_ws = [Const "s_0"];
  tgt_ws = [Val 146; Const "s_0"];
  user_instrs = []
}

let sk = [

  "Words on source stack are set correctly">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_0 in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [Consts.mk_user_const "s_0"]
        ps.src_ws
    );

  "Empty source stack">:: (fun _ ->
      let ps = Params.mk Instruction.predef {ups_0 with src_ws = []} in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        []
        ps.src_ws
    );

  "Words on target stack are set correctly">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_0 in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [Z3util.num 146; Consts.mk_user_const "s_0"]
        ps.tgt_ws
    );

  "Empty target stack">:: (fun _ ->
      let ps = Params.mk Instruction.predef {ups_0 with tgt_ws = []} in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        []
        ps.tgt_ws
    );

  ]

let add_1 = {
  id = "ADD_1";
  opcode = "00";
  disasm = "ADD";
  inpt_sk = [Const "s_0"; Val 1];
  outpt_sk = [Const "s_1"];
  gas = 3;
}

let ups_1 =
  { n = 4;
    k = 3;
    ss = ["s_0"; "s_1"];
    src_ws = [Const "s_0"];
    tgt_ws = [Val 146; Const "s_1"];
    user_instrs = [add_1]
  }

let timestamp = {
  id = "TIMESTAMP";
  opcode = "42";
  disasm = "TIMESTAMP";
  inpt_sk = [];
  outpt_sk = [Const "s_2"];
  gas = 2;
}

let ups_2 =
  { n = 4;
    k = 3;
    ss = ["s_0"; "s_1"; "s_2"];
    src_ws = [Const "s_0"];
    tgt_ws = [Const "s_2"; Const "s_1"];
    user_instrs = [add_1; timestamp]
  }


let user_instrs = [

  "No user_instrs">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_0 in
      assert_equal
        ~cmp:[%eq: int] ~printer:[%show: int]
        (List.length Instruction.predef)
        (List.length ps.instrs)
    );

  "One user_instrs">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_1 in
      assert_equal
        ~cmp:[%eq: int] ~printer:[%show: int]
        ((List.length Instruction.predef) + 1)
        (List.length ps.instrs)
    );

  "Two user_instrs">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_2 in
      assert_equal
        ~cmp:[%eq: int] ~printer:[%show: int]
        ((List.length Instruction.predef) + 2)
        (List.length ps.instrs)
    );

  "Find predefined instruction PUSH32">:: (fun _ ->
      let id = "PUSH32" in
      let ps = Params.mk Instruction.predef ups_1 in
      let iota = Params.find_instr ps ~id:"PUSH32" in
      assert_equal
        ~cmp:[%eq: string] ~printer:[%show: string]
        id
        iota.id
    );

  "Find userdefined instruction ADD_1">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_1 in
      let iota = Params.find_instr ps ~id:"ADD_1" in
      assert_equal
        ~cmp:[%eq: string] ~printer:[%show: string]
        "ADD_1"
        iota.id
    );

  "Contains instr with id ADD_1">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_1 in
      assert_bool ""
        (List.exists ps.instrs ~f:(fun iota -> iota.id = "ADD_1"))
    );

  "Instruction with id ADD_1 has correct gas and opcode">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_1 in
      let iota = List.find_exn ps.instrs ~f:(fun iota -> iota.id = "ADD_1") in
      assert_bool ""
        (iota.gas = add_1.gas && iota.opcode = add_1.opcode)
    );

  "Contains instr with id TIMESTAMP">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_2 in
      assert_bool ""
        (List.exists ps.instrs ~f:(fun iota -> iota.id = "TIMESTAMP"))
    );
]

let int_map = [

  "Converting predefined instruction PUSH32 from int and back is idempotent">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_0 in
      let iota = Params.find_instr ps ~id:"PUSH32" in
      let i = Params.instr_to_int ps iota in
      assert_equal
        ~cmp:[%eq: int] ~printer:[%show: int]
        i
        (Params.instr_to_int ps (Params.instr_of_int ps i))
    );

  "Converting int to predefined instruction PUSH32 and back is idempotent">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_0 in
      let iota = Params.find_instr ps ~id:"PUSH32" in
      assert_equal
        ~cmp:[%eq: string] ~printer:[%show: string]
        iota.id
        (Params.instr_of_int ps (Params.instr_to_int ps iota)).id
    );

  "Converting userdefined instruction ADD_1 from int and back is idempotent">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_1 in
      let iota = Params.find_instr ps ~id:"ADD_1" in
      let i = Params.instr_to_int ps iota in
      assert_equal
        ~cmp:[%eq: int] ~printer:[%show: int]
        i
        (Params.instr_to_int ps (Params.instr_of_int ps i))
    );

  "Converting int to userdefined instruction ADD_1 and back is idempotent">:: (fun _ ->
      let ps = Params.mk Instruction.predef ups_1 in
      let iota = Params.find_instr ps ~id:"ADD_1" in
      assert_equal
        ~cmp:[%eq: string] ~printer:[%show: string]
        iota.id
        (Params.instr_of_int ps (Params.instr_to_int ps iota)).id
    );
]

let gas_grouping =
  [
  ]

let input = "{
  \"max_progr_len\": 4,
  \"max_sk_sz\": 3,
  \"vars\": [ \"s(0)\", \"s(1)\" ],
  \"src_ws\": [ \"s(0)\" ],
  \"tgt_ws\": [ 146, \"s(1)\" ],
  \"user_instrs\": [
    {
      \"id\": \"ADD_1\",
      \"opcode\": \"00\",
      \"disasm\": \"ADD\",
      \"inpt_sk\": [ \"s(0)\", 1 ],
      \"outpt_sk\": [ \"s(1)\" ],
      \"gas\": 3
    }
  ]
}
"

let from_string = [

  "Read input from user params">:: (fun _ ->
      let ups = User_params.user_params_of_yojson_exn (Yojson.Safe.from_string input) in
      let ps = Params.mk Instruction.predef ups in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [Consts.mk_user_const "s(0)"]
        ps.src_ws
    );


]

let suite = "suite" >::: sk @ user_instrs @ int_map @ gas_grouping @ from_string

let () =
  run_test_tt_main suite
