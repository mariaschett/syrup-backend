open Core
open Z3util
open Consts

(* word from user *)
type user_w =
  Val of int
| Const of user_const [@@deriving yojson]

(* user defined instruction *)
type user_instr = {
  id : string;
  opcode : string;
  disasm : string;
  input_stack : user_w list;
  output_stack : user_w list;
} [@@deriving yojson]

type user_params = {
  n : int;
  k : int;
  ss : user_const list;
  src_ws : user_w list;
  tgt_ws : user_w list;
  user_instrs : user_instr list;
} [@@deriving yojson]

let mk_from_user_w = function
  | Val v -> num v
  | Const c -> mk_user_const c

let mk_userdef_instr iota =
  let alpha = List.length iota.input_stack in
  let delta = List.length iota.output_stack in
  let effect _ j =
    let open Z3Ops in
    conj (List.mapi iota.input_stack ~f:(fun i w -> mk_x i j == mk_from_user_w w)) &&
    conj (List.mapi iota.output_stack ~f:(fun i w -> mk_x' i j == mk_from_user_w w))
  in
  Instruction.mk iota.id alpha delta effect

let to_params predef ui =
  let src_ws = List.map ui.src_ws ~f:mk_from_user_w in
  let tgt_ws = List.map ui.tgt_ws ~f:mk_from_user_w in
  let ss =  List.map ui.ss ~f:Consts.mk_user_const in
  let instrs = predef @ (List.map ui.user_instrs ~f:mk_userdef_instr) in
  Params.mk ~n:ui.n ~k:ui.k ~src_ws:src_ws ~tgt_ws:tgt_ws ~ss:ss instrs
