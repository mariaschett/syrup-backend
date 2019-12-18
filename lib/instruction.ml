open Core
open Z3util
open Consts
open Sk_util

type t = {
  id : string;
  opcode : string;
  disasm : string;
  effect : int -> int -> Z3.Expr.expr;
  gas : int;
} [@@deriving show {with_path = false}]

let mk ~id ~opcode ~effect ~gas ~disasm = {
  id = id;
  opcode = opcode;
  disasm = disasm;
  effect = effect;
  gas = gas;
}

let enc_userdef ~in_ws ~out_ws ~alpha ~delta k j =
  let diff = alpha - delta in
  let x i = mk_x i j and x' i = mk_x' i j in
  let u i = mk_u i j and u_l i = mk_u (k-1-i) j in
  let open Z3Ops in
  let effect =
    conj (List.mapi in_ws ~f:(fun i w -> u i && x i == w)) &&
    conj (List.mapi out_ws ~f:(fun i w -> x' i == w)) &&
    conj (List.init (Int.max 0 diff) ~f:(fun i -> ~! (u_l i)))
  in
  enc_prsv k j diff alpha && enc_sk_utlz k j diff && effect

let mk_userdef id ~in_ws ~out_ws ~opcode ~gas ~disasm =
  let delta = List.length in_ws and alpha = List.length out_ws in
  mk ~id ~effect:(enc_userdef ~in_ws ~out_ws ~delta ~alpha) ~opcode ~gas ~disasm

(* predefined instructions *)

let mk_PUSH =
  mk ~id:"PUSH" ~opcode:"60" ~disasm:"PUSH" ~gas:3
    ~effect:(fun k j ->
      let a = mk_a j in
      enc_userdef ~in_ws:[] ~out_ws:[a] ~alpha:1 ~delta:0 k j
    )

let is_PUSH iota = iota.id = "PUSH"

let mk_POP =
  mk ~id:"POP" ~opcode:"50" ~gas:2 ~disasm:"POP"
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j in
        enc_userdef ~in_ws:[x_0] ~out_ws:[] ~alpha:0 ~delta:1 k j
      )

let mk_SWAP =
  (* opcode for SWAP I *)
  mk ~id:"SWAP" ~opcode:"90" ~disasm:"SWAP" ~gas:3
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j and x_1 = mk_x 1 j in
        enc_userdef ~in_ws:[x_0; x_1] ~out_ws:[x_1; x_0] ~alpha:2 ~delta:2 k j
      )

let mk_DUP =
  (* opcdoe for DUP I *)
  mk ~id:"DUP" ~opcode:"80" ~disasm:"DUP" ~gas:3
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j in
        enc_userdef ~in_ws:[x_0] ~out_ws:[x_0; x_0] ~alpha:2 ~delta:1 k j
      )

let mk_NOP =
  mk ~id:"NOP" ~opcode:"" ~disasm:"NOP" ~gas:0
    ~effect:(fun k j ->
        enc_userdef ~in_ws:[] ~out_ws:[] ~alpha:0 ~delta:0 k j
      )

let predef =
  [mk_PUSH; mk_POP; mk_SWAP; mk_DUP; mk_NOP]

(* show instruction *)

let show_disasm ?arg:(arg=None) iota =
  iota.disasm ^ (Option.value_map arg ~default:"" ~f:(fun i -> " " ^ Z.to_string i))

let show_opcode ?arg:(arg=None) iota =
  iota.opcode ^ (Option.value_map arg ~default:"" ~f:(fun i -> Z.format "x" i))

let hex_add base idx =
  Z.add (Z.of_string_base 16 base) (Z.of_int (idx-1)) |>
  Z.format "x"
