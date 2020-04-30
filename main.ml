open Core
open Opti
open Outpt
 
type output_options =
  { write_only : bool
  ; slvr : slvr option
  ; omit_csv_header : bool
  }

let exec_slvr ?ignore_exit_cd:(ignore_exit_cd=false) ~call_to_slvr enc =
  let (in_chn, out_chn) as chn = Unix.open_process call_to_slvr in
  Out_channel.output_string out_chn enc;
  Out_channel.close out_chn;
  let rslt = In_channel.input_all in_chn in
  match Unix.close_process chn with
  | Ok () -> rslt
  | Error e ->
    if ignore_exit_cd
    then rslt
    else failwith (Sexp.to_string (Unix.Exit_or_signal.sexp_of_error e))

let outputcfg =
  ref {write_only = false; slvr = None; omit_csv_header = false}

let set_options write_only slvr omit_csv_header =
  outputcfg := {write_only = write_only; slvr = slvr; omit_csv_header = omit_csv_header}

let () =
  let open Command.Let_syntax in
  Command.basic ~summary:"opti: an optimizer"
    [%map_open
      let
        write_only = flag "write-only" no_arg
          ~doc:"print smt constraint in SMT-LIB format, a mapping to instructions, and objectives"
      and slvr = flag "solver"
          (optional (Arg_type.create slvr_of_string))
          ~doc:"S choose solver: Z3 | BCLT | OMS"
      and path_to_slvr = flag "path"
          (optional_with_default "z3" (Arg_type.create Fn.id))
          ~doc:"P give path to binary of corresponding solver"
      and timeout = flag "timeout"
          (optional_with_default 0 (Arg_type.create int_of_string))
          ~doc:"TO set timeout in seconds"
      and omit_csv_header = flag "omit-csv-header" no_arg
          ~doc:"omit writing the csv header of the output"
      and print_slvr_outpt = flag "print-solver-output" no_arg
          ~doc:"print the output of the solver"
      and scale_progr_len = flag "scale-progr-len"
          (optional_with_default 100 (Arg_type.create int_of_string))
          ~doc:"give scale of program length in percent, e.g., 50 for half, 200 for double"
      and scale_sk_sz = flag "scale-sk-sz"
          (optional_with_default 100 (Arg_type.create int_of_string))
          ~doc:"give scale of stack size in percent, e.g., 200 for double"
      and rm_tgt_instr = flag "rm-tgt-instr" no_arg
          ~doc:"remove constraint to force instruction in target program"
      and add_tgt_instr = flag "add-tgt-instr" no_arg
          ~doc:"add constraint to force at instruction at most once in target program"
      and
        fn = anon ("USER_PARAMS" %: string)
      in
      fun () ->
        set_options write_only slvr omit_csv_header;
        (* parse user parameters from json *)
        let user_params = User_params.user_params_of_yojson_exn (Yojson.Safe.from_file fn) in
        (* create parameters for encoding *)
        let params = Params.mk ~scale_progr_len ~scale_sk_sz Instruction.predef user_params in
        (* compute encodings *)
        let enc = Enc.enc_block ~rm_tgt_instr ~add_tgt_instr params in
        let enc_weights = Enc.enc_weight params in
        let obj = Z3util.get_objectives enc enc_weights in
        (* write files *)
        let path = Filename.dirname fn in
        (* solve *)
        match slvr with
        | None ->
          let mdl = Z3util.solve_max_model_exn enc enc_weights in
          write_model (path^"/model") mdl;
          Yojson.Safe.to_file (path^"/result.json") (Print_trgt.trgt_prgrm_to_yojson (Print_trgt.show_trgt_prgrm mdl obj params))
        | Some slvr ->
          let enc = show_smt slvr enc enc_weights timeout in
          if write_only
          then write_all ~slvr ~path ~enc ~obj ~params
          else
            let slvr_outpt =
              match slvr with
              | Z3 ->
                let call_to_slvr = path_to_slvr ^ " -in " in
                exec_slvr ~call_to_slvr enc ~ignore_exit_cd:true
              | BCLT ->
                let call_to_slvr = path_to_slvr ^ " -tlimit " ^ [%show: int] timeout ^ " -success false " in
                exec_slvr ~call_to_slvr enc ~ignore_exit_cd:true
              | OMS ->
                let call_to_slvr = path_to_slvr in
                exec_slvr ~call_to_slvr enc ~ignore_exit_cd:true
            in
            let rslt = parse_slvr_outpt slvr_outpt slvr fn params in
            (* count system and user time of child process to also count memory allocation etc.
               get actual time used by process *)
            let slvr_time_in_sec = (let t = Unix.times () in (t.tms_cutime +. t.tms_cstime)) in
            let csv = show_csv rslt omit_csv_header slvr_time_in_sec in
            Out_channel.print_endline csv;
            if print_slvr_outpt
            then Out_channel.print_endline slvr_outpt
            else ()
    ]
  |> Command.run ~version:"0.0"
