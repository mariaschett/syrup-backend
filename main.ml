open Core
open Opti
open Outpt
 
type output_options =
  { pmodel : bool
  ; psmt : bool
  ; slvr : slvr option
  }

let exec_slvr call_to_slvr enc =
  let (in_chn, out_chn) as chn = Unix.open_process call_to_slvr in
  Out_channel.output_string out_chn enc;
  Out_channel.close out_chn;
  let rslt = In_channel.input_all in_chn in
  match Unix.close_process chn with
  | Ok () -> rslt
  | Error e -> failwith (Sexp.to_string (Unix.Exit_or_signal.sexp_of_error e))

let outputcfg =
  ref {pmodel = false; psmt = false; slvr = None}

let set_options pm psmt slvr =
  outputcfg := {pmodel = pm; psmt = psmt; slvr = slvr}

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"opti: an optimizer"
    [%map_open
      let p_model = flag "print-model" no_arg
          ~doc:"print model found by solver"
      and p_smt = flag "print-smt" no_arg
          ~doc:"print constraint given to solver in SMT-LIB format"
      and slvr = flag "solver"
          (optional (Arg_type.create slvr_of_string))
          ~doc:"choose solver Z3 | BCLT"
      and
        fn = anon ("USER_PARAMS" %: string)
      in
      fun () ->
        set_options p_model p_smt slvr;
        (* parse user parameters from json *)
        let user_params = User_params.user_params_of_yojson_exn (Yojson.Safe.from_file fn) in
        (* create parameters for encoding *)
        let params = Params.mk Instruction.predef user_params in
        (* compute encodings *)
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let obj = Z3util.get_objectives enc enc_weights in
        let enc_z3 = show_smt Z3 enc enc_weights in
        let enc_bclt = show_smt BCLT enc enc_weights in
        (* write files *)
        let path = Filename.dirname fn in
        write_smt Z3 ~path ~data:enc_z3;
        write_smt BCLT ~path ~data:enc_bclt;
        write_map (path^"/instruction") params;
        write_objectives (path^"/objectives") ~data:obj;
        (* solve *)
        let time_out = "10" in
        match slvr with
        | None ->
          let mdl = Z3util.solve_max_model_exn enc enc_weights in
          write_model (path^"/model") mdl;
          Yojson.Safe.to_file (path^"/result.json") (Outpt.result_to_yojson (show_result mdl obj params))
        | Some slvr ->
          match slvr with
          | Z3 ->
            let result = exec_slvr ("z3 -T:"^ time_out ^" -in ") enc_z3
            in Out_channel.write_all (path^"/"^ (string_of_slvr slvr) ^".outpt") ~data:result
          | _ -> failwith "not implemented yet"
    ]
  |> Command.run ~version:"0.0"
