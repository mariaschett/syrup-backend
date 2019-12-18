open Core
open Opti
open Outpt
open Z3util
 
type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let outputcfg =
  ref {pmodel = false; psmt = false;}

let set_options pm psmt =
  outputcfg := {pmodel = pm; psmt = psmt;}

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"opti: an optimizer"
    [%map_open
      let p_model = flag "print-model" no_arg
          ~doc:"print model found by solver"
      and p_smt = flag "print-smt" no_arg
          ~doc:"print constraint given to solver in SMT-LIB format"
      and
        fn = anon ("USER_PARAMS" %: string)
      in
      fun () ->
        set_options p_model p_smt;
        (* parse user parameters from json *)
        let user_params = User_params.user_params_of_yojson_exn (Yojson.Safe.from_file fn) in
        (* create parameters for encoding *)
        let params = Params.mk Instruction.predef user_params in
        let enc = Enc.enc_block params in
        let enc_weights = Enc.enc_weight params in
        let _ = Z3util.add_soft_constraints enc_weights in
        let _ = Z3.Optimize.add !octxt [enc] in
        let path = (Filename.dirname fn) in
        write_smt (path^"/encoding_z3") ~data:(show_z3_smt ());
        write_smt (path^"/encoding_bclt") ~data:(show_blcg_smt ());
        write_map (path^"/instruction") params;
        write_objectives (path^"/objectives");
        let _ = Z3.Optimize.check !octxt in
        let mdl = Option.value_exn (Z3.Optimize.get_model !octxt) in
        write_model (path^"/model") mdl;
        Yojson.Safe.to_file (path^"/result.json") (Outpt.result_to_yojson (show_result mdl params))
    ]
  |> Command.run ~version:"0.0"
