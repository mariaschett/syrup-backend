open Core
open Consts
open Params

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

(* pretty print target program from t_i/a_i list *)

let dec_instr_from_slvr ts params i =
  let t_i = List.Assoc.find_exn ts ("t_" ^ [%show: int] i) ~equal:(=) in
  instr_of_int params (Int.of_string t_i)

let dec_arg_from_slvr as_ i =
  let a_i = List.Assoc.find_exn as_ ("a_" ^ [%show: int] i) ~equal:(=) in
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

(* pretty print from internal model *)

type trgt_prgrm = {
  opcode : string;
  disasm : string;
  cost : string;
} [@@deriving yojson]

let dec_arg mdl i =
  let a_i = Z3util.eval_const mdl (mk_a i) in
  Z.of_string (Z3.Arithmetic.Integer.numeral_to_string a_i)

let dec_instr mdl params i =
  let t_i = Z3util.eval_const mdl (mk_t i) in
  instr_of_int params (Big_int.int_of_big_int (Z3.Arithmetic.Integer.get_big_int t_i))

let show_disasm_mdl mdl params = show_disasm params
    ~dec_instr:(dec_instr mdl params)
    ~dec_arg:(dec_arg mdl)

let show_opcode_mdl mdl params = show_opcode params
    ~dec_instr:(dec_instr mdl params)
    ~dec_arg:(dec_arg mdl)

let show_trgt_prgrm mdl obj params =
  { opcode = [%show: string list] (show_opcode_mdl mdl params );
    disasm = [%show: string list] (show_disasm_mdl mdl params);
    cost = [%show: int] (Z3util.solve_objectives mdl obj);
  }
