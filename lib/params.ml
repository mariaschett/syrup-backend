open Core
open Instruction

type params = {
  instrs : Instruction.t list;
  map : (Instruction.t * int) list;
  k : int;
  n : int;
}

let mk ~k:k ~n:n instrs =
  let map = List.mapi instrs ~f:(fun i iota -> (iota, i)) in
  { instrs = instrs; map = map; k; n}

let enc_instr_name params iota =
  List.Assoc.find_exn (params.map) iota ~equal:(fun i1 i2 -> i1.name = i2.name) |> Z3util.num

let show_map params = [%show: (string * int) list] (List.map params.map ~f:(fun (iota, i) -> (iota.name, i)))

let nop_enc_name params =
  let (_, i) = List.find_exn (params.map) ~f:(fun (iota, _) -> iota.name = "NOP")
  in i
