open Core
open Z3util
open Consts

type user_word =
  | Val of Z.t
  | Const of user_const

let user_word_to_yojson = function
  | Val i -> [%to_yojson: string] (Z.to_string i)
  | Const c -> [%to_yojson: string] c

let user_word_of_yojson = function
  | `Int i -> Ok (Val (Z.of_int i))
  | `Intlit i -> Ok (Val (Z.of_string i))
  | `String s -> Ok (Const s)
  | _ -> Error "Cannot parse word. Either variable (string) or value (int) required."

let enc_user_word = function
  | Val v -> bignum v
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

let mk_user_instr ui =
  Instruction.mk_userdef ui.id ~opcode:ui.opcode ~gas:ui.gas ~disasm:ui.disasm
    ~in_ws:(List.map ui.inpt_sk ~f:enc_user_word)
    ~out_ws:(List.map ui.outpt_sk ~f:enc_user_word)

type user_params = {
  n : int [@key "max_progr_len"];
  k : int [@key "max_sk_sz"];
  ss : user_const list [@key "vars"];
  src_ws : user_word list;
  tgt_ws : user_word list;
  current_cost : int;
  user_instrs : user_instr list;
} [@@deriving yojson { exn = true }]

let mk_ws = List.map ~f:enc_user_word
