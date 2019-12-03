open Core
open Z3util

let show_smt ex =
  let smt = Z3.SMT.benchmark_to_smtstring !ctxt "" "" "unknown" "" [] ex in
  (* hack get model *)
  smt ^ "(get-model)"

let write_smt_and_map fn ex params =
  let ex' = show_smt ex in
  Out_channel.write_all (fn^".smt") ~data:ex';
  Out_channel.write_all (fn^".map") ~data:(Params.show_map params)
