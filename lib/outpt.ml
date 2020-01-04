open Core
open Consts
open Params

type slvr =
    Z3
  | BCLT
  | OMS

let slvr_of_string = function
  | "Z3" -> Z3
  | "BCLT" -> BCLT
  | "OMS" -> OMS
  | _ -> failwith "Unknown solver."

let string_of_slvr = function
  | Z3 -> "z3"
  | BCLT -> "bclt"
  | OMS -> "oms"

let show_z3_smt cmn_smt =
  cmn_smt ^
  (* hack to get objectives, there should be an API call *)
  "(get-objectives)\n"

let show_oms_smt cmn_smt =
  let open String.Search_pattern in
  (* optiMaxSAT requires to have (minimize gas) before (check sat) *)
  let cmn_smt' =
    let mg = "(check-sat)" in let mg' = "(minimize gas)\n" ^ mg in
    replace_all ~in_:cmn_smt (create mg) ~with_:mg'
  in
  cmn_smt' ^ "(get-objectives)\n"

let show_blct_smt cmn_smt =
  let open String.Search_pattern in
  (* barcelogic requires different start of assert-soft *)
  let op = "assert-soft (" and op' = "assert-soft (! (" in
  (* barcelogic requires additional ) of assert-soft *)
  let cp =  "gas)" and  cp' = "gas))" in
  let replacd_op = replace_all (create op) ~in_:cmn_smt ~with_:op' in
  replace_all ~in_:replacd_op (create cp) ~with_:cp'

let show_smt slvr enc enc_weights =
  let cmn_smt =
    (* hack to set logic, there should be an API call *)
    "(set-logic QF_LIA)\n" ^
    Z3util.show_smt enc enc_weights
  in match slvr with
  | Z3 -> show_z3_smt cmn_smt
  | BCLT -> show_blct_smt cmn_smt
  | OMS -> show_oms_smt cmn_smt

let write_smt ~data ~path slvr =
  let fn = path ^ "/encoding_" ^ (string_of_slvr slvr) ^ ".smt2" in
  Out_channel.write_all ~data fn

let write_map fn params =
  Out_channel.write_all (fn^".map") ~data:(Params.show_instr_to_int params)

let write_model fn mdl =
  Out_channel.write_all (fn^".smt2") ~data:(Z3.Model.to_string mdl)

let write_objectives fn ~data:obj =
  Out_channel.write_all (fn^".smt2") ~data:(Z3.Expr.to_string obj)

(* pretty print output *)

type rslt =
  | TIMEOUT
  | OPTIMAL of int
  | UB of int (* UpperBound *)
  | MISC of string
[@@deriving show {with_path = false}]

let ws = [%sedlex.regexp? Star white_space]
let digits = [%sedlex.regexp? Plus '0'..'9']

let match_int buf =
  let open Sedlexing in
  match%sedlex buf with
  | digits -> Int.of_string (Latin1.lexeme buf)
  | _ -> failwith "Failed to parse int."

let output_z3 outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws -> OPTIMAL (match_int buf)
  | "unknown", ws, "(objectives", ws, "(gas", ws, "(interval 0", ws -> UB (match_int buf)
  | "timeout" -> TIMEOUT
  | _ -> MISC outpt

let output_bclt outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | ws, "(optimal", ws -> OPTIMAL (match_int buf)
  | ws, "(cost", ws -> UB (match_int buf)
  | ws, "unknown" -> TIMEOUT
  | _ -> MISC outpt

let output_oms outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws -> OPTIMAL (match_int buf)
  | ws, "(objectives", ws, "(gas unknown), range: [ 0, +INF ]" -> TIMEOUT
  | ws, "(objectives", ws, "(gas ", digits, "), partial search, range: [ 0,", ws -> UB (match_int buf)
  | _ -> MISC outpt

(* pretty print from model *)

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

type result = {
  opcode : string;
  disasm : string;
  cost : string;
} [@@deriving yojson]

let show_result mdl obj params =
  { opcode = [%show: string list] (show_opcode mdl params);
    disasm = [%show: string list] (show_disasm mdl params);
    cost = [%show: int] (Z3util.solve_objectives mdl obj);
  }
