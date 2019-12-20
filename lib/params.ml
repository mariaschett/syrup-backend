open Core
open Instruction

type params = {
  instrs : Instruction.t list;
  instr_int_map : (Instruction.t * int) list;
  k : int;
  n : int;
  max_wsz : Z.t;
  src_ws : Z3.Expr.expr list; (* words on source stack, top of stack at postion 0 *)
  tgt_ws : Z3.Expr.expr list;
  ss : Z3.Expr.expr list; (* "forall quantified" variables *)
}

let mk predef user_params =
  let open User_params in
  let max_wsz = Z.pow (Z.of_int 2) 256 in
  let instrs =  predef ~k:user_params.k @ (List.map user_params.user_instrs ~f:User_params.mk_user_instr) in
  let map = List.mapi instrs ~f:(fun i iota -> (iota, i)) in
  { instrs = instrs;
    instr_int_map = map;
    k = user_params.k;
    n = user_params.n;
    max_wsz = max_wsz;
    src_ws = User_params.mk_ws user_params.src_ws;
    tgt_ws = User_params.mk_ws user_params.tgt_ws;
    ss = List.map user_params.ss ~f:Consts.mk_user_const;
  }

let find_instr params ~id =
  List.find_exn params.instrs ~f:(fun iota -> iota.id = id)

let instr_of_int params i =
  List.Assoc.find_exn (List.Assoc.inverse (params.instr_int_map)) i ~equal:(=)

let instr_to_int params iota =
  List.Assoc.find_exn (params.instr_int_map) iota ~equal:(fun i1 i2 -> i1.id = i2.id)

let show_instr_to_int params =
  let show_pair (iota, i) = iota.id ^ " : " ^ [%show: int] i ^ "; " in
  List.fold params.instr_int_map ~init:"" ~f:(fun m im -> m ^ (show_pair im))

let group_instr_by_gas params =
  List.fold params.instrs ~init:Core.Int.Map.empty
    ~f:(fun m iota -> Map.add_multi m ~key:iota.gas ~data:iota)
  |> Int.Map.to_alist ~key_order:`Increasing
