open Core
open Z3util
open Consts

type user_word =
  | Val of int
  | Const of user_const

let user_word_to_yojson = function
  | Val i -> [%to_yojson: int] i
  | Const c -> [%to_yojson: string] c

let user_word_of_yojson = function
  | `Int i -> Ok (Val i)
  | `String s -> Ok (Const s)
  | _ -> Error "Cannot parse word. Either variable (string) or value (int) required."

let enc_user_word = function
  | Val v -> num v
  | Const c -> mk_user_const c

(* user defined instruction *)
type user_instr = {
  id : string;
  opcode : string;
  disasm : string;
  inpt_sk : user_word list;
  outpt_sk : user_word list;
  gas : int;
} [@@deriving yojson]

type user_params = {
  n : int [@key "max_progr_len"];
  k : int [@key "max_sk_sz"];
  ss : user_const list [@key "vars"];
  src_ws : user_word list;
  tgt_ws : user_word list;
  user_instrs : user_instr list;
} [@@deriving yojson { exn = true }]

let mk_userdef_instr ui =
  let in_ws= List.map ui.inpt_sk ~f:enc_user_word in
  let out_ws = List.map ui.outpt_sk ~f:enc_user_word in
  Instruction.mk_userdef ui.id ~opcode:ui.opcode ~gas:ui.gas ~in_ws ~out_ws

let to_params predef ui =
  let src_ws = List.map ui.src_ws ~f:enc_user_word in
  let tgt_ws = List.map ui.tgt_ws ~f:enc_user_word in
  let ss =  List.map ui.ss ~f:Consts.mk_user_const in
  let instrs = predef @ (List.map ui.user_instrs ~f:mk_userdef_instr) in
  Params.mk ~n:ui.n ~k:ui.k ~src_ws:src_ws ~tgt_ws:tgt_ws ~ss:ss instrs

let read_inpt fn =
  let user_params = user_params_of_yojson_exn (Yojson.Safe.from_file fn) in
  let bn = Filename.chop_extension (Filename.basename fn) in
  (bn, user_params)
