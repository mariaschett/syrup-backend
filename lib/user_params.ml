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
  commutative : bool;
  gas : int;
} [@@deriving yojson]

let mk_user_instr tgt_ws ui =
  let out_ws = List.map ui.outpt_sk ~f:enc_user_word in
  let iota =
    Instruction.mk_userdef ui.id ~opcode:ui.opcode ~gas:ui.gas ~disasm:ui.disasm ~is_commutative:ui.commutative
      ~in_ws:(List.map ui.inpt_sk ~f:enc_user_word)
      ~out_ws
  in
  let in_tgt_ws out_ws = List.exists out_ws ~f:(List.mem tgt_ws ~equal:Z3.Expr.equal) in
  let in_tgt_opt = if in_tgt_ws out_ws then Some iota else None in
  (iota, in_tgt_opt)

type user_params = {
  n : int [@key "max_progr_len"];
  k : int [@key "max_sk_sz"];
  ss : user_const list [@key "vars"];
  src_ws : user_word list;
  tgt_ws : user_word list;
  init_progr_len : int;
  curr_cst : int [@key "current_cost"];
  user_instrs : user_instr list;
} [@@deriving yojson { exn = true }]

let mk_ws = List.map ~f:enc_user_word
