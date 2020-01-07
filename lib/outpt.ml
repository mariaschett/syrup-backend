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

let write_all ~path ~slvr ~enc ~obj ~params =
  write_smt slvr ~path ~data:enc;
  write_map (path^"/instruction") params;
  write_objectives (path^"/objectives") ~data:obj;

(* pretty print output *)

type rslt =
  | TIMEOUT
  | OPTIMAL of int
  | RANGE of int * int
  | MISC of string
[@@deriving show {with_path = false}]

let ws = [%sedlex.regexp? Star white_space]
let digits = [%sedlex.regexp? Plus '0'..'9']

let parse_int buf =
  let open Sedlexing in
  match%sedlex buf with
  | digits -> Int.of_string (Latin1.lexeme buf)
  | _ -> failwith "Failed to parse int."

let parse_gas_rslt_z3 rslt =
  let open Sedlexing in
  let buf = Latin1.from_string rslt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws -> OPTIMAL (parse_int buf)
  | "unknown", ws, "(objectives", ws, "(gas", ws, "(interval", ws ->
    let lb = parse_int buf in
    let ub =  match%sedlex buf with | ws -> parse_int buf | _ -> failwith "Parse error." in
    RANGE (lb, ub)
  | "timeout" -> TIMEOUT
  | _ -> MISC rslt

let parse_gas_rslt_bclt rslt =
  let open Sedlexing in
  let buf = Latin1.from_string rslt in
  match%sedlex buf with
  | ws, "(optimal", ws -> OPTIMAL (parse_int buf)
  | ws, "(cost", ws -> RANGE (0, parse_int buf)
  | ws, "unknown" -> TIMEOUT
  | _ -> MISC rslt

let parse_gas_rslt_oms rslt =
  let open Sedlexing in
  let buf = Latin1.from_string rslt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws -> OPTIMAL (parse_int buf)
  | ws, "(objectives", ws, "(gas unknown), range: [ 0, +INF ]" -> TIMEOUT
  | ws, "(objectives", ws, "(gas ", digits, "), partial search, range: [", ws ->
    let lb = parse_int buf in
    let ub =  match%sedlex buf with | ",", ws -> parse_int buf | _ -> failwith "Parse error." in
    RANGE (lb, ub)
  | _ -> MISC rslt

let parse_gas_rslt rslt = function
  | Z3 -> parse_gas_rslt_z3 rslt
  | BCLT -> parse_gas_rslt_bclt rslt
  | OMS -> parse_gas_rslt_oms rslt

(* produce result json *)

type outpt = {
  lower_bound : int option;
  upper_bound : int option;
  shown_optimal : bool;
  timed_out : bool;
  current_cost : int;
} [@@deriving yojson { exn = true } ]

let outpt_json (params : params) (gas_rslt : rslt) =
  let (lower_bound, upper_bound) = match gas_rslt with RANGE (lb, ub) -> (Some lb, Some ub) | _ -> (None, None) in
  let (shown_optimal, lower_bound, upper_bound) = match gas_rslt with OPTIMAL b -> (true, Some b, Some b) | _ -> (false, lower_bound, upper_bound) in
  let timed_out = match gas_rslt with TIMEOUT -> true | _ -> false in
  let outpt =
    { lower_bound = lower_bound;
      upper_bound = upper_bound;
      shown_optimal = shown_optimal;
      timed_out = timed_out;
      current_cost = params.curr_cst;
    }
  in
  outpt_to_yojson outpt

(* pretty print from model *)

let dec_arg mdl i =
  let a_i = Z3util.eval_const mdl (mk_a i) in
  Z.of_string (Z3.Arithmetic.Integer.numeral_to_string a_i)

let dec_instr mdl params i =
  let t_i = Z3util.eval_const mdl (mk_t i) in
  instr_of_int params (Big_int.int_of_big_int (Z3.Arithmetic.Integer.get_big_int t_i))

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

type trgt_prgrm = {
  opcode : string;
  disasm : string;
  cost : string;
} [@@deriving yojson]

let show_trgt_prgrm mdl obj params =
  { opcode = [%show: string list] (show_opcode mdl params);
    disasm = [%show: string list] (show_disasm mdl params);
    cost = [%show: int] (Z3util.solve_objectives mdl obj);
  }
