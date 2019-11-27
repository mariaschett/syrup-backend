open Core
open Opti
open Z3util
open Consts
open Instruction

type output_options =
  { pmodel : bool
  ; psmt : bool
  }

let predef = [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

let params_block_192 =
  let s_1 = mk_s 1 (* =^= ADD_1 *) in
  let s_0 = mk_s 0 (* =^= input variable on stack *) in
  let mk_add_1 = mk_userdef "ADD_1" ~in_ws:[s_0; num 1] ~out_ws:[s_1] in
  Params.mk (predef @ [mk_add_1]) ~k:3 ~n:4 ~src_ws:[s_0] ~tgt_ws:[num 146; s_1] ~ss:[s_1; s_0]

let params_block_ex1 =
  Params.mk predef ~k:3 ~n:2 ~src_ws:[] ~tgt_ws:[num 146] ~ss:[]

let params_block_ex2 =
  let s_0 = mk_s 0 (* =^= input variable on stack *) in
  Params.mk predef ~k:3 ~n:3 ~src_ws:[s_0] ~tgt_ws:[s_0; s_0] ~ss:[s_0]

let params_block_192_rev =
  let s_1 = mk_s 1 (* =^= ADD_1 *) in
  let s_0 = Z3util.intconst ("s_0") (* =^= input variable on stack *) in
  let mk_add_1 = mk_userdef "ADD_1" ~in_ws:[num 1; s_0] ~out_ws:[s_1] in
  Params.mk (predef @ [mk_add_1]) ~k:3 ~n:4 ~src_ws:[s_0] ~tgt_ws:[num 146; s_1] ~ss:[s_1; s_0]

let show_smt ex =
  let smt = Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" [] ex in
  (* hack get model *)
  smt ^ "(get-model)"

let write_smt_and_map fn ex params =
  let ex' = show_smt ex in
  Out_channel.write_all ("examples/"^fn^".smt") ~data:ex';
  Out_channel.write_all ("examples/"^fn^".map") ~data:(Params.show_map params)

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
      in
      fun () ->
        let all =
          [("block_192", params_block_192);
           ("block_192_rev", params_block_192_rev);
           ("block_ex1", params_block_ex1);
           ("block_ex2", params_block_ex2)] in
        set_options p_model p_smt;
        List.fold all ~init:() ~f:(fun _ (name, params) ->
            let enc = Enc.enc_block params in
            write_smt_and_map name enc params)

    ]
  |> Command.run ~version:"0.0"
