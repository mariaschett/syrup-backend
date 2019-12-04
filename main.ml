open Core
open Opti
open Instruction
open Inpt
open Outpt

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
        let (bn, up) = read_inpt fn in
        let params = to_params predef up in
        let _ = Enc.enc_weight params in
        let enc = Enc.enc_block params in
        write_smt_and_map ("examples/"^bn) enc params

    ]
  |> Command.run ~version:"0.0"
