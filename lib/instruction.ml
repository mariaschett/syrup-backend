open Core
open Z3util
open Consts
open Sk_util

type t = {
  id : string;
  opcode : string;
  effect : int -> int -> Z3.Expr.expr;
  gas : int;
} [@@deriving show {with_path = false}]

let mk ~id ~opcode ~effect ~gas = {
  id = id;
  opcode = opcode;
  effect = effect;
  gas = gas;
}

let show_disasm ?arg:(arg=None) iota =
  iota.id ^ (Option.value_map arg ~default:"" ~f:(fun i -> " " ^ Z.to_string i))

let show_opcode ?arg:(arg=None) iota =
  iota.opcode ^ (Option.value_map arg ~default:"" ~f:(fun i -> Z.format "x" i))

let hex_add base idx =
  Z.add (Z.of_string_base 16 base) (Z.of_int (idx-1)) |>
  Z.format "x"

let enc_push diff alpha idx k j  =
  let x'_0 = mk_x' 0 j in
  let u_k = mk_u (k-1) j in
  let a = mk_a j in
  (* to choose the "optimal" sized PUSH *)
  let lb = bignum (Z.pow (Z.of_int 2) ((idx - 1) * 8)) in
  let ub = bignum (Z.pow (Z.of_int 2) (idx * 8)) in
  let open Z3Ops in
  ~! u_k &&
  (lb <= a) && (a < ub) &&
  (x'_0 == a && enc_prsv k j diff alpha && enc_sk_utlz k j diff)

let mk_PUSH idx =
  let id = "PUSH" ^ ([%show: int] idx) in
  let alpha = 1 and delta = 0 in
  let diff = alpha - delta in
  mk ~id ~effect:(enc_push diff alpha idx) ~opcode:(hex_add "60" idx) ~gas:3

let is_PUSH iota = String.is_substring iota.id ~substring:"PUSH"

let enc_userdef ~in_ws:in_ws ~out_ws:out_ws diff alpha k j =
  let x i = mk_x i j and x' i = mk_x' i j in
  let u i = mk_u i j and u_l i = mk_u (k-1-i) j in
  let open Z3Ops in
  let effect =
    conj (List.mapi in_ws ~f:(fun i w -> u i && x i == w)) &&
    conj (List.mapi out_ws ~f:(fun i w -> ~! (u_l i) && x' i == w))
  in
  enc_prsv k j diff alpha && enc_sk_utlz k j diff && effect

let mk_userdef id ~in_ws ~out_ws ~opcode ~gas =
  let delta = List.length in_ws and alpha = List.length out_ws in
  let diff = alpha - delta in
  mk ~id ~effect:(enc_userdef ~in_ws ~out_ws diff alpha)  ~opcode ~gas

(* predefined instructions *)

let enc_pop diff alpha k j =
  let x_0 = mk_x 0 j in
  enc_userdef ~in_ws:[x_0] ~out_ws:[] diff alpha k j

let mk_POP =
  let id = "POP" in
  let alpha = 0 and delta = 1 in
  let diff = alpha - delta in
  mk ~id ~effect:(enc_pop diff alpha) ~opcode:"50" ~gas:2

let enc_swap diff alpha k j =
  let x_0 = mk_x 0 j and x_1 = mk_x 1 j in
  let x'_0 = mk_x' 0 j and x'_1 = mk_x' 1 j in
  let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
  let open Z3Ops in
  u_0 && u_1 &&
  ((x'_0 == x_1) && (x'_1 == x_0)) && enc_prsv k j diff alpha && enc_sk_utlz k j diff

let mk_SWAP =
  let id = "SWAP" in
  let alpha = 2 and delta = 2 in
  let diff = alpha - delta in
  (* opcode for SWAP I *)
  mk ~id ~effect:(enc_swap diff alpha) ~opcode:"90" ~gas:3

let enc_dup diff alpha k j =
  let x_0 = mk_x 0 j in
  enc_userdef ~in_ws:[x_0] ~out_ws:[x_0; x_0] diff alpha k j

let mk_DUP =
  let id = "DUP" in
  let alpha = 2 and delta = 1 in
  let diff = alpha - delta in
  (* opcdoe for DUP I *)
  mk ~id ~effect:(enc_dup diff alpha) ~opcode:"80" ~gas:3

let enc_nop diff alpha k j =
  enc_userdef ~in_ws:[] ~out_ws:[] diff alpha k j

let mk_NOP =
  let id = "NOP" in
  let alpha = 0 and delta = 0 in
  let diff = alpha - delta in
  mk ~id ~effect:(enc_nop diff alpha) ~opcode:"" ~gas:0

let predef =
  let pushs = List.init 32 ~f:(fun i -> mk_PUSH (i+1)) in
  pushs @ [mk_POP; mk_SWAP; mk_DUP; mk_NOP]
