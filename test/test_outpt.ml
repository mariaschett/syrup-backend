open OUnit2
open Syrup_backend
open Instruction

let shows = [

  "Show opcode of PUSH1 1">:: (fun _ ->
      assert_equal
        ~cmp:[%eq: string]
        ~printer:[%show: string]
        "6001"
        (show_opcode mk_PUSH ~arg:(Some (Z.of_int 1)))
    );

  "Show opcode of PUSH12">:: (fun _ ->
      assert_equal
        ~cmp:[%eq: string]
        ~printer:[%show: string]
        "6b400000000000000000000000"
        (show_opcode mk_PUSH ~arg:(Some (Z.pow (Z.of_int 2) 94)))
    );

  "Show opcode of PUSH32">:: (fun _ ->
      assert_equal
        ~cmp:[%eq: string]
        ~printer:[%show: string]
        "7f8000000000000000000000000000000000000000000000000000000000000000"
        (show_opcode mk_PUSH ~arg:(Some (Z.pow (Z.of_int 2) 255)))
    );

    "Show disasm of PUSH1 1">:: (fun _ ->
      assert_equal
        ~cmp:[%eq: string]
        ~printer:[%show: string]
        "PUSH1 1"
        (show_disasm mk_PUSH ~arg:(Some (Z.of_int 1)))
    );

  "Show opcode of PUSH12">:: (fun _ ->
      assert_equal
        ~cmp:[%eq: string]
        ~printer:[%show: string]
        "PUSH12 19807040628566084398385987584"
        (show_disasm mk_PUSH ~arg:(Some (Z.pow (Z.of_int 2) 94)))
    );

  "Show opcode of PUSH32">:: (fun _ ->
      assert_equal
        ~cmp:[%eq: string]
        ~printer:[%show: string]
        "PUSH32 57896044618658097711785492504343953926634992332820282019728792003956564819968"
        (show_disasm mk_PUSH ~arg:(Some (Z.pow (Z.of_int 2) 255)))
    );
]

let suite = "suite" >::: shows

let () =
  run_test_tt_main suite
