open Core
open Z3util
open Consts
open Params

let write_smt_and_map fn params =
  let show_smt =
    (* hack get model *)
    (Z3.Optimize.to_string !octxt) ^ "(get-model)\n(get-objectives)"
  in
  Out_channel.write_all (fn^".smt") ~data:(show_smt);
  Out_channel.write_all (fn^".map") ~data:(Params.show_instr_to_int params)

let write_model fn mdl =
  Out_channel.write_all (fn^".model") ~data:(Z3.Model.to_string mdl)

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

let write_disasm fn cnstrs params =
  let data = show_disasm cnstrs params in
  Out_channel.write_all (fn^".disasm") ~data:([%show: string list] data);
