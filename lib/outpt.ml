open Core
open Params
open Sexplib
open Print_trgt

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

(* print output in csv *)

type rslt = {
  block_id : string;
  target_gas_cost : int option;
  shown_optimal : bool;
  no_model_found : bool;
  source_gas_cost : int;
  saved_gas: int option;
  target_disasm : string option;
  target_opcode : string option;
} [@@deriving show]

let mk_default_rslt block_id params =
  {
    block_id = block_id;
    target_gas_cost = None;
    shown_optimal = false;
    saved_gas = None;
    no_model_found = false;
    source_gas_cost = params.curr_cst;
    target_disasm = None;
    target_opcode = None;
  }

let ws = [%sedlex.regexp? Star white_space]
let digits = [%sedlex.regexp? Plus '0'..'9']
let remainder = [%sedlex.regexp? Star any]

let parse_int buf =
  let open Sedlexing in
  match%sedlex buf with
  | digits -> Int.of_string (Latin1.lexeme buf)
  | _ -> failwith "Failed to parse int."

let parse_remainder buf =
  let open Sedlexing in
  match%sedlex buf with
  | remainder -> Latin1.lexeme buf
  | _ -> failwith "Parse error."

let set_target_gas_cost trgt prtl_rslt =
  { prtl_rslt with
    target_gas_cost = Some trgt.cost;
    target_disasm = Some trgt.disasm;
    target_opcode = Some trgt.opcode;
  }

let set_optimal trgt prtl_rslt =
  let prtl_rslt' = set_target_gas_cost trgt prtl_rslt in
  {prtl_rslt' with shown_optimal = true}

let set_no_model_found prtl_rslt =
  { prtl_rslt with no_model_found = true}

let rec find_consts_Z3 const = function
  | Sexp.Atom _ -> []
  | Sexp.List [Sexp.Atom "define-fun";
               Sexp.Atom id;
               Sexp.List _ ;
               Sexp.Atom "Int"; Sexp.Atom vl]
    when String.is_prefix id ~prefix:(const ^ "_") -> [(id, vl)]
  | Sexp.List ss -> List.concat_map ss ~f:(find_consts_Z3 const)

let parse_target_Z3 params mdl =
  let exp = Sexp.of_string mdl in
  let ts = find_consts_Z3 "t" exp and as_ = find_consts_Z3 "a" exp in
  trgt_prgrm_from_slvr params ts as_

let parse_slvr_outpt_z3 params outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws ->
    let _ = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws, ")" ->
        let mdl = parse_remainder buf in
        let trgt = parse_target_Z3 params mdl in
        set_optimal trgt
      | _ -> failwith "Parse error."
    end
  | "unknown", ws, "(objectives", ws, "(gas", ws, "(interval", ws, digits ->
    let _ = match%sedlex buf with | ws -> parse_int buf | _ -> failwith "Parse error." in
    begin
      match%sedlex buf with
      | ws, ")", ws, ")", ws, ")", ws, "(model" ->
        let mdl =  "(model" ^ parse_remainder buf in
        let trgt = parse_target_Z3 params mdl in
        set_target_gas_cost trgt
      | ws, ")", ws, ")", ws, ")", ws, "(error" ->
        set_no_model_found
      | _ -> failwith "Parse error."
    end
  | "timeout" -> set_no_model_found
  | _ -> Fn.id

let parse_target_BCLT = parse_target_Z3

let parse_slvr_outpt_bclt params outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | ws, "(optimal", ws ->
    let _ = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws ->
        let mdl = parse_remainder buf in
        let trgt = parse_target_BCLT params mdl in
        set_optimal trgt
      | _ -> failwith "Parse error."
    end
  | ws, "(cost", ws ->
    let _ = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws ->
        let mdl = parse_remainder buf in
        let trgt = parse_target_BCLT params mdl in
        set_target_gas_cost trgt
      | _ -> failwith "Parse error."
    end
  | ws, "unknown" -> set_no_model_found
  | _ -> Fn.id

let rec find_consts_OMS const = function
  | Sexp.Atom _ -> []
  | Sexp.List [Sexp.Atom id;
               Sexp.Atom vl]
    when String.is_prefix id ~prefix:(const ^ "_") -> [(id, vl)]
  | Sexp.List ss -> List.concat_map ss ~f:(find_consts_OMS const)

let parse_target_OMS params mdl =
  let exp = Sexp.of_string mdl in
  let ts = find_consts_OMS "t" exp and as_ = find_consts_OMS "a" exp in
  trgt_prgrm_from_slvr params ts as_

let parse_slvr_outpt_oms params outpt =
  let open Sedlexing in
  let buf = Latin1.from_string outpt in
  match%sedlex buf with
  | "sat", ws, "(objectives", ws, "(gas", ws ->
    let _ = parse_int buf in
    begin
      match%sedlex buf with
      | ws, ")", ws, ")", ws ->
        let mdl = parse_remainder buf in
        let trgt = parse_target_OMS params mdl in
        set_optimal trgt
      | _ -> failwith "Parse error."
    end
  | ws, "(objectives", ws, "(gas ", digits, "), partial search, range: [", ws, digits ->
    let _ =  match%sedlex buf with | ",", ws -> parse_int buf | _ -> failwith "Parse error." in
    begin
      match%sedlex buf with
      | ws, "]", ws, ")", ws ->
        let mdl = parse_remainder buf in
        let trgt = parse_target_OMS params mdl in
        set_target_gas_cost trgt
      |  _ -> failwith "Parse error."
    end
  | ws, "(objectives", ws, "(gas unknown), range: [ 0, +INF ]" -> set_no_model_found
  | _ -> Fn.id

let parse_slvr_outpt outpt slvr block_id params =
  let dflt_rslt = mk_default_rslt block_id params in
  let prtl_rslt = match slvr with
    | Z3 -> parse_slvr_outpt_z3 params outpt dflt_rslt
    | BCLT -> parse_slvr_outpt_bclt params outpt dflt_rslt
    | OMS -> parse_slvr_outpt_oms params outpt dflt_rslt
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
    "target_disasm";
    "target_opcode"
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
     (Option.value_map ~default:"" ~f:([%show: string]) rslt.target_disasm);
     (Option.value_map ~default:"" ~f:([%show: string]) rslt.target_opcode);
    ]
  in
  (if omit_csv_header then "" else show_csv_header) ^
  (String.concat ~sep:"," data)
