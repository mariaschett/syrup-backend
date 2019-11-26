open Core
open Instruction

type params = {
  instrs : Instruction.t list;
  map : (Instruction.t * Z.t) list;
  k : int;
  n : int;
  max_wsz : Z.t;
}

let mk ~k:k ~n:n instrs =
  let max_wsz = Z.pow (Z.of_int 2) 10 in
  let map = List.mapi instrs ~f:(fun i iota -> (iota, Z.add max_wsz (Z.of_int i))) in
  { instrs = instrs; map = map; k = k; n = n; max_wsz = max_wsz }

let enc_instr_name params iota =
  List.Assoc.find_exn (params.map) iota ~equal:(fun i1 i2 -> i1.name = i2.name) |> Z3util.bignum

let show_map params =
  let show_pair (iota, i) = iota.name ^ " : " ^ Z.to_string i ^ "; " in
  List.fold params.map ~init:"" ~f:(fun m im -> m ^ (show_pair im))

let nop_enc_name params =
  let (_, i) = List.find_exn (params.map) ~f:(fun (iota, _) -> iota.name = "NOP")
  in i
