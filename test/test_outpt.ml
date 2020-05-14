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
