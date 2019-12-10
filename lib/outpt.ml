open Core
open Z3util

let show_smt enc =
  let _ = Z3.Optimize.add !octxt [enc] in
  (* hack get model *)
  (Z3.Optimize.to_string !octxt) ^  "(get-model)"

let write_smt_and_map fn cnstrs params =
  Out_channel.write_all (fn^".smt") ~data:(show_smt cnstrs);
  Out_channel.write_all (fn^".map") ~data:(Params.show_instr_to_int params)
