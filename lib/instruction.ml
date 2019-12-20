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

(* show instruction *)

let is_PUSH iota = iota.id = "PUSH"

let show_hex arg =
  let hx = Z.format "x" arg in
  if Int.rem (String.length hx) 2 = 1 then "0" ^ hx else hx

let compute_idx arg = String.length (show_hex arg) / 2

let show_disasm ?arg:(arg=None) iota =
  let idx = if is_PUSH iota then [%show: int] (compute_idx (Option.value_exn arg)) else "" in
  iota.disasm ^ idx ^ (Option.value_map arg ~default:"" ~f:(fun i -> " " ^ Z.to_string i))

let hex_add base idx =
  Z.add (Z.of_string_base 16 base) (Z.of_int idx) |>
  Z.format "x"

let show_opcode ?arg:(arg=None) iota =
  if is_PUSH iota
  then
    let arg = Option.value_exn arg in
    let idx = compute_idx arg in
    (hex_add iota.opcode (idx-1) ^ (show_hex arg))
  else iota.opcode

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

let mk_POP =
  mk ~id:"POP" ~opcode:"50" ~gas:2 ~disasm:"POP"
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j in
        enc_userdef ~in_ws:[x_0] ~out_ws:[] ~alpha:0 ~delta:1 k j
      )

let mk_SWAP idx =
  let disasm = ("SWAP" ^ [%show: int] idx) in
  let opcode = hex_add "90" (idx-1) in
  mk ~id:disasm ~opcode ~disasm:disasm ~gas:3
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j and x_l = mk_x idx j in
        let prsvd = List.map ~f:(fun i -> mk_x i j)
            (List.range ~start:`inclusive 1 ~stop:`exclusive idx) in
        enc_userdef ~in_ws:([x_0] @ prsvd @ [x_l]) ~out_ws:([x_l] @ prsvd @ [x_0])
          ~alpha:(idx+1) ~delta:(idx+1) k j
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
  [mk_PUSH; mk_POP; mk_SWAP 1; mk_DUP; mk_NOP]
