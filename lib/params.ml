(*   Copyright 2020 Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Core
open Instruction

type params = {
  instrs : Instruction.t list;
  instrs_in_tgt : Instruction.t list;
  instr_int_map : (Instruction.t * int) list;
  k : int;
  n : int;
  max_wsz : Z.t;
  src_ws : Z3.Expr.expr list; (* words on source stack, top of stack at postion 0 *)
  tgt_ws : Z3.Expr.expr list;
  ss : Z3.Expr.expr list; (* "forall quantified" variables *)
  curr_cst : int;
}

let mk predef user_params =
  let open User_params in
  let max_wsz = Z.pow (Z.of_int 2) 256 in
  let tgt_ws = User_params.mk_ws user_params.tgt_ws in
  let predef_instrs = predef ~k:user_params.k in
  let (userdef_instrs, instrs_in_tgt_opt) =
     List.map user_params.user_instrs ~f:(User_params.mk_user_instr tgt_ws) |> List.unzip in
  let instrs = predef_instrs @ userdef_instrs in
  let map = List.mapi instrs ~f:(fun i iota -> (iota, i)) in
  let n = if user_params.init_progr_len <= 0 then 1 else user_params.init_progr_len in
  { instrs = instrs;
    instrs_in_tgt = List.filter_opt instrs_in_tgt_opt;
    instr_int_map = map;
    k = user_params.k;
    n = n;
    max_wsz = max_wsz;
    src_ws = User_params.mk_ws user_params.src_ws;
    tgt_ws = tgt_ws;
    ss = List.map user_params.ss ~f:Consts.mk_user_const;
    curr_cst = user_params.curr_cst;
  }

let find_instr params ~id =
  List.find_exn params.instrs ~f:(fun iota -> String.equal iota.id id)

let instr_of_int params i =
  List.Assoc.find_exn (List.Assoc.inverse (params.instr_int_map)) i ~equal:(=)

let instr_to_int params iota =
  List.Assoc.find_exn (params.instr_int_map) iota ~equal:(fun i1 i2 -> String.equal i1.id i2.id)

let show_instr_to_int params =
  let show_pair (iota, i) = iota.id ^ " : " ^ [%show: int] i ^ "; " in
  List.fold params.instr_int_map ~init:"" ~f:(fun m im -> m ^ (show_pair im))

let group_instr_by_gas params =
  List.fold params.instrs ~init:Core.Int.Map.empty
    ~f:(fun m iota -> Map.add_multi m ~key:iota.gas ~data:iota)
  |> Int.Map.to_alist ~key_order:`Increasing

let group_instr_combine_expensive params =
  let most_expensive_instr = List.max_elt (Instruction.predef ~k:params.k)
      ~compare:(fun iota1 iota2 -> Int.compare iota1.gas iota2.gas) in
  let max_gas = (Option.value_exn most_expensive_instr).gas in
  let (below, above) = List.fold (group_instr_by_gas params) ~init:([],[])
      ~f:(fun (below, above) (i, instrs) ->
          if i > max_gas
          then (below,  above @ [(i, instrs)])
          else (below @ [(i, instrs)], above))
  in below @ [(max_gas + 1, List.concat_map above ~f:(fun (_, instrs) -> instrs)) ]
