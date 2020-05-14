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
open Core
open Consts
open Params

type trgt_prgrm = {
  opcode : string;
  disasm : string;
  cost : int;
} [@@deriving yojson]

(* pretty print target program *)

let show_disasm params ~dec_instr ~dec_arg =
  let arg iota i = Option.some_if (Instruction.is_PUSH iota) (dec_arg i) in
  List.init params.n ~f:(fun i ->
      let iota = dec_instr i in
      Instruction.show_disasm iota ~arg:(arg iota i)
    )

let show_opcode params ~dec_instr ~dec_arg =
  let arg iota i = Option.some_if (Instruction.is_PUSH iota) (dec_arg i) in
  List.init params.n ~f:(fun i ->
      let iota = dec_instr i in
      Instruction.show_opcode iota ~arg:(arg iota i)
    )

let compute_cost params ~dec_instr =
  List.init params.n ~f:(dec_instr) |>
  List.sum (module Int) ~f:(Instruction.get_gas)

(* pretty print target program from t_i/a_i list *)

let dec_instr_from_slvr ts params i =
  let t_i = List.Assoc.find_exn ts ("t_" ^ [%show: int] i) ~equal:String.equal in
  instr_of_int params (Int.of_string t_i)

let dec_arg_from_slvr as_ i =
  let a_i = List.Assoc.find_exn as_ ("a_" ^ [%show: int] i) ~equal:String.equal in
  Z.of_string a_i

let show_disasm_from_slvr params ts as_ =
  show_disasm params
    ~dec_instr:(dec_instr_from_slvr ts params)
    ~dec_arg:(dec_arg_from_slvr as_)
  |> String.concat ~sep:" "

let show_opcode_from_slvr params ts as_ =
  show_opcode params
    ~dec_instr:(dec_instr_from_slvr ts params)
    ~dec_arg:(dec_arg_from_slvr as_)
  |> String.concat

let compute_cost_from_slvr params ts =
  compute_cost  params
    ~dec_instr:(dec_instr_from_slvr ts params)

let trgt_prgrm_from_slvr params ts as_ =
  {
    opcode = show_opcode_from_slvr params ts as_;
    disasm = show_disasm_from_slvr params ts as_;
    cost = compute_cost_from_slvr params ts;
  }

(* pretty print from internal model *)

let dec_arg mdl i =
  let a_i = Z3util.eval_const mdl (mk_a i) in
  Z.of_string (Z3.Arithmetic.Integer.numeral_to_string a_i)

let dec_instr mdl params i =
  let t_i = Z3util.eval_const mdl (mk_t i) in
  instr_of_int params (Z.to_int (Z3.Arithmetic.Integer.get_big_int t_i))

let show_disasm_mdl mdl params = show_disasm params
    ~dec_instr:(dec_instr mdl params)
    ~dec_arg:(dec_arg mdl)

let show_opcode_mdl mdl params = show_opcode params
    ~dec_instr:(dec_instr mdl params)
    ~dec_arg:(dec_arg mdl)

let show_trgt_prgrm mdl obj params =
  { opcode = [%show: string list] (show_opcode_mdl mdl params );
    disasm = [%show: string list] (show_disasm_mdl mdl params);
    cost = Z3util.solve_objectives mdl obj;
  }
