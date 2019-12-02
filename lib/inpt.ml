open Core
open Z3util
open Consts

(* word from user *)
type user_w =
  | Val of int
  | Const of user_const

let user_w_to_yojson = function
  | Val i -> [%to_yojson: int] i
  | Const c -> [%to_yojson: string] c

let user_w_of_yojson w =
 match w with
  | `Int i -> Ok (Val i)
  | `String s -> Ok (Const s)
  | _ -> Error "Cannot parse word. Either variable (string) or value (int) required."

(* user defined instruction *)
type user_instr = {
  id : string;
  opcode : string;
  disasm : string;
  inpt_sk : user_w list;
  outpt_sk : user_w list;
  gas : int;
} [@@deriving yojson]

type user_params = {
  n : int [@key "max_progr_len"];
  k : int [@key "max_sk_sz"];
  ss : user_const list [@key "vars"];
  src_ws : user_w list;
  tgt_ws : user_w list;
  user_instrs : user_instr list;
} [@@deriving yojson { exn = true }]

let mk_from_user_w = function
  | Val v -> num v
  | Const c -> mk_user_const c

let mk_userdef_instr iota =
  let alpha = List.length iota.inpt_sk in
  let delta = List.length iota.outpt_sk in
  let effect _ j =
    let open Z3Ops in
    conj (List.mapi iota.inpt_sk ~f:(fun i w -> mk_x i j == mk_from_user_w w)) &&
    conj (List.mapi iota.outpt_sk ~f:(fun i w -> mk_x' i j == mk_from_user_w w))
  in
  Instruction.mk ~id:iota.id ~alpha ~delta ~effect ~opcode:iota.opcode ~gas:iota.gas

let to_params predef ui =
  let src_ws = List.map ui.src_ws ~f:mk_from_user_w in
  let tgt_ws = List.map ui.tgt_ws ~f:mk_from_user_w in
  let ss =  List.map ui.ss ~f:Consts.mk_user_const in
  let instrs = predef @ (List.map ui.user_instrs ~f:mk_userdef_instr) in
  Params.mk ~n:ui.n ~k:ui.k ~src_ws:src_ws ~tgt_ws:tgt_ws ~ss:ss instrs
