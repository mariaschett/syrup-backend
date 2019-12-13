open Core
open Opti
open Instruction
open Inpt
open Outpt
open Z3util
 
type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let predef = [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

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
        let ups = user_params_of_yojson_exn (Yojson.Safe.from_file fn) in
        (* create parameters for encoding *)
        let params = Params.mk ~n:ups.n ~k:ups.k
            ~src_ws:(mk_ws ups.src_ws) ~tgt_ws:(mk_ws ups.tgt_ws)
            ~ss:(List.map ups.ss ~f:Consts.mk_user_const)
            (predef @ (List.map ups.user_instrs ~f:mk_user_instr)) in
        let enc = Enc.enc_block params in
        let _ = Enc.enc_weight params in
        let _ = Z3.Optimize.add !octxt [enc] in
        let bn = Filename.chop_extension (Filename.basename fn) in
        write_smt_and_map ("examples/"^bn) params;
        let _ = Z3.Optimize.check !octxt in
        let mdl = Option.value_exn (Z3.Optimize.get_model !octxt) in
        write_model ("examples/"^bn) mdl;
        write_disasm ("examples/"^bn) mdl params

    ]
  |> Command.run ~version:"0.0"
