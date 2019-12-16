open Core
open Z3util
open Consts
open Params

let show_z3_smt () =
  (* hack to set logic, there should be an API call *)
  "(set-logic QF_LIA)\n"^
  (Z3.Optimize.to_string !octxt)
  (* hack to get model, there should be an API call *)
  ^ "(get-model)\n"
  (* hack to get objectives, there should be an API call *)
  ^ "(get-objectives)"

let show_blcg_smt () =
  let open String.Search_pattern in
  (* barcelogic requires different start of assert-soft *)
  let op = "assert-soft (" and op' = "assert-soft (! (" in
  (* barcelogic requires additional ) of assert-soft *)
  let cp =  "gas)" and  cp' = "gas))" in
  let replacd_op = replace_all (create op) ~in_:(show_z3_smt ()) ~with_:op' in
  replace_all ~in_:replacd_op (create cp) ~with_:cp'

let write_smt fn ~data =
  Out_channel.write_all (fn^".smt2") ~data:data

let write_map fn params =
  Out_channel.write_all (fn^".map") ~data:(Params.show_instr_to_int params)

let write_model fn mdl =
  Out_channel.write_all (fn^".smt2") ~data:(Z3.Model.to_string mdl)

let dec_arg mdl i =
  let a_i = Z3util.eval_const mdl (mk_a i) in
  Z.of_string (Z3.Arithmetic.Integer.numeral_to_string a_i)

let dec_instr mdl params i =
  let t_i = Z3util.eval_const mdl (mk_t i) in
  instr_of_int params (Z3.Arithmetic.Integer.get_int t_i)

let show_disasm mdl params =
  let arg iota i = Option.some_if (Instruction.is_PUSH iota) (dec_arg mdl i) in
  List.init params.n ~f:(fun i ->
      let iota = dec_instr mdl params i in
      Instruction.show_disasm iota ~arg:(arg iota i)
    )

let show_opcode mdl params =
  let arg iota i = Option.some_if (Instruction.is_PUSH iota) (dec_arg mdl i) in
  List.init params.n ~f:(fun i ->
      let iota = dec_instr mdl params i in
      Instruction.show_opcode iota ~arg:(arg iota i)
    )

let show_cost mdl = Z3.Expr.to_string (Z3util.eval_obj mdl)

type result = {
  opcode : string;
  disasm : string;
  cost : string;
} [@@deriving yojson]

let show_result mdl params =
  { opcode = [%show: string list] (show_opcode mdl params);
    disasm = [%show: string list] (show_disasm mdl params);
    cost = [%show: string] (show_cost mdl);
  }
