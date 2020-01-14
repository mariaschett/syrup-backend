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
  | Z3 -> "Z3"
  | BCLT -> "BCLT"
  | OMS -> "OMS"

let show_smt_Z3 cmn_smt =
  cmn_smt ^
  (* hack to get objectives, there should be an API call *)
  "(get-objectives)\n" ^
  "(get-model)\n"

let show_smt_BCLT cmn_smt =
  let open String.Search_pattern in
  (* barcelogic requires different start of assert-soft *)
  let op = "assert-soft (" and op' = "assert-soft (! (" in
  (* barcelogic requires additional ) of assert-soft *)
  let cp =  "gas)" and  cp' = "gas))" in
  let replacd_op = replace_all (create op) ~in_:cmn_smt ~with_:op' in
  (replace_all ~in_:replacd_op (create cp) ~with_:cp') ^
  "(get-model)\n"

let show_smt_OMS cmn_smt =
  let open String.Search_pattern in
  (* optiMaxSAT requires to have (minimize gas) before (check sat) *)
  let cmn_smt' =
    let mg = "(check-sat)" in let mg' = "(minimize gas)\n" ^ mg in
    replace_all ~in_:cmn_smt (create mg) ~with_:mg'
  in
  "(set-option :produce-models true)\n" ^ cmn_smt' ^
  "(get-objectives)\n" ^
  "(load-objective-model -1)\n" ^
  "(get-model)\n"

let show_smt slvr enc enc_weights timeout =
  let cmn_smt =
    (* hack to set logic, there should be an API call *)
    "(set-logic QF_LIA)\n" ^
    Z3util.show_smt enc enc_weights
  in match slvr with
  | Z3 ->
    let timeout_in_ms = timeout * 1000 in
    "(set-option :timeout " ^ [%show: int] timeout_in_ms ^ ".0)\n" ^ (show_smt_Z3 cmn_smt)
  | BCLT -> show_smt_BCLT cmn_smt
  | OMS -> "(set-option :timeout " ^ [%show: int] timeout ^".0)\n" ^
           (show_smt_OMS cmn_smt)

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

type rslt = {
  block_id : string;
  target_gas_cost : int option;
  shown_optimal : bool;
  no_model_found : bool;
  source_gas_cost : int;
  saved_gas: int option;
  slvr_outpt : string;
} [@@deriving show]

let mk_default_rslt block_id params outpt =
  {
    block_id = block_id;
    target_gas_cost = None;
    shown_optimal = false;
    saved_gas = None;
    no_model_found = false;
    source_gas_cost = params.curr_cst;
    slvr_outpt = outpt;
  }

let ws = [%sedlex.regexp? Star white_space]
let digits = [%sedlex.regexp? Plus '0'..'9']

let parse_int buf =
  let open Sedlexing in
  match%sedlex buf with
  | digits -> Int.of_string (Latin1.lexeme buf)
  | _ -> failwith "Failed to parse int."

let set_optimal bound prtl_rslt =
  {prtl_rslt with
     target_gas_cost = Some bound;
     shown_optimal = true
  }

let set_target_gas_cost target_gas_cost prtl_rslt =
  { prtl_rslt with
     target_gas_cost = Some target_gas_cost;
  }

let set_no_model_found prtl_rslt =
  { prtl_rslt with no_model_found = true}

let parse_slvr_outpt_z3 outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws ->
    let optimal = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws, ")" ->
        let _ = Latin1.lexeme buf in
        set_optimal optimal
      | _ -> failwith "Parse error."
    end
  | "unknown", ws, "(objectives", ws, "(gas", ws, "(interval", ws, digits ->
    let upper_bound =  match%sedlex buf with | ws -> parse_int buf | _ -> failwith "Parse error." in
    begin
      match%sedlex buf with
      | ws, ")", ws, ")", ws, ")", ws, "(model" ->
        let _ = "(model" ^ (Latin1.lexeme buf) in
        set_target_gas_cost upper_bound
      | ws, ")", ws, ")", ws, ")", ws, "(error" ->
        set_no_model_found
      | _ -> failwith "Parse error."
    end
  | "timeout" -> set_no_model_found
  | _ -> Fn.id

let parse_slvr_outpt_bclt outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | ws, "(optimal", ws ->
    let optimal = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws ->
        let _ = Latin1.lexeme buf in
        set_optimal optimal
      | _ -> failwith "Parse error."
    end
  | ws, "(cost", ws ->
    let upper_bound = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws ->
        let _ = Latin1.lexeme buf in
        set_target_gas_cost upper_bound
      | _ -> failwith "Parse error."
    end
  | ws, "unknown" -> set_no_model_found
  | _ -> Fn.id

let parse_slvr_outpt_oms outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws ->
    let optimal = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws, ")", ws ->
        let _ = Latin1.lexeme buf in
        set_optimal optimal
      | _ -> failwith "Parse error."
    end
  | ws, "(objectives", ws, "(gas ", digits, "), partial search, range: [", ws, digits ->
    let upper_bound =  match%sedlex buf with | ",", ws -> parse_int buf | _ -> failwith "Parse error." in
    begin
      match%sedlex buf with
      | ws, "]", ws, ")", ws ->
        let _ = Latin1.lexeme buf in
        set_target_gas_cost upper_bound
      |  _ -> failwith "Parse error."
    end
  | ws, "(objectives", ws, "(gas unknown), range: [ 0, +INF ]" -> set_no_model_found
  | _ -> Fn.id

let parse_slvr_outpt outpt slvr block_id params =
  let dflt_rslt = mk_default_rslt block_id params outpt in
  let prtl_rslt = match slvr with
    | Z3 -> parse_slvr_outpt_z3 outpt dflt_rslt
    | BCLT -> parse_slvr_outpt_bclt outpt dflt_rslt
    | OMS -> parse_slvr_outpt_oms outpt dflt_rslt
  in
  let saved_gas = Option.map ~f:(fun ub -> Int.max (prtl_rslt.source_gas_cost - ub) 0) prtl_rslt.target_gas_cost in
  {prtl_rslt with saved_gas = saved_gas}

let show_csv_header =
  let csv_header = [
    "block_id";
    "target_gas_cost";
    "shown_optimal";
    "no_model_found";
    "source_gas_cost";
    "saved_gas";
    "solver_time_in_sec";
    "solver_output";
  ]
  in
  (String.concat ~sep:"," csv_header) ^ "\n"

let show_csv rslt omit_csv_header slvr_time_in_sec =
  let data =
    [rslt.block_id;
     (Option.value_map ~default:"" ~f:([%show: int]) rslt.target_gas_cost);
     [%show: bool] rslt.shown_optimal;
     [%show: bool] rslt.no_model_found;
     [%show: int] rslt.source_gas_cost;
     (Option.value_map ~default:"0" ~f:([%show: int]) rslt.saved_gas);
     [%show: float] slvr_time_in_sec;
     "\"" ^  rslt.slvr_outpt ^ "\"";
    ]
  in
  (if omit_csv_header then "" else show_csv_header) ^
  (String.concat ~sep:"," data)

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
