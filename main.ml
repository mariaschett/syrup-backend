open Core
open Opti
open Outpt
 
type output_options =
  { pmodel : bool
  ; psmt : bool
  ; slvr : slvr
  }

let outputcfg =
  ref {pmodel = false; psmt = false; slvr = Z3}

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
          (optional_with_default Z3 (Arg_type.create slvr_of_string))
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
        (* write files *)
        let path = Filename.dirname fn in
        write_smt Z3 ~path ~data:(show_z3_smt enc enc_weights);
        write_smt BCLT ~path ~data:(show_blcg_smt enc enc_weights);
        write_map (path^"/instruction") params;
        write_objectives (path^"/objectives") ~data:obj;
        let mdl = Z3util.solve_max_model_exn enc enc_weights in
        write_model (path^"/model") mdl;
        Yojson.Safe.to_file (path^"/result.json") (Outpt.result_to_yojson (show_result mdl obj params))
    ]
  |> Command.run ~version:"0.0"
