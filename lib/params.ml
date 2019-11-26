open Core
open Instruction

type params = {
  instrs : Instruction.t list;
  map : (Instruction.t * int) list;
  k : int;
  n : int;
  ss : Z3.Expr.expr list;
  max_wsz : Z.t;
}

let mk ~k:k ~n:n ~forall:ss instrs =
  let max_wsz = Z.pow (Z.of_int 2) 256 in
  let map = List.mapi instrs ~f:(fun i iota -> (iota, i)) in
  { instrs = instrs; map = map; k = k; n = n; ss = ss; max_wsz = max_wsz }

let enc_instr_name params iota =
  List.Assoc.find_exn (params.map) iota ~equal:(fun i1 i2 -> i1.name = i2.name) |> Z3util.num

let show_map params = [%show: (string * int) list] (List.map params.map ~f:(fun (iota, i) -> (iota.name, i)))

let nop_enc_name params =
  let (_, i) = List.find_exn (params.map) ~f:(fun (iota, _) -> iota.name = "NOP")
  in i
