open Core

type params = {
  instrs : Instruction.t list;
  map : (Instruction.t * int) list;
}

let mk instrs =
  let map = List.mapi instrs ~f:(fun i iota -> (iota, i)) in
  { instrs = instrs; map = map }

let enc_instr_name params iota =
  List.Assoc.find_exn (params.map) iota ~equal:(=) |> Z3util.num

let show_map params = [%show: (Instruction.t * int) list] params.map
