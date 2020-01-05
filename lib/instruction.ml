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

let is_PUSH iota = String.equal iota.id "PUSH"

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

let enc_semtc ~in_ws ~is_commutative ~out_ws ~alpha ~delta k j =
  let out_idxs = List.range ~start:`inclusive (k - alpha + delta) ~stop:`exclusive k in
  let x i = mk_x i j and x' i = mk_x' i j in
  let u i = mk_u i j in
  let in_ws' = if is_commutative then Helper.permutations in_ws else [in_ws] in
  let open Z3Ops in
  conj (List.mapi in_ws ~f:(fun i _ -> u i)) &&
  disj (List.map in_ws' ~f:(fun ws -> conj (List.mapi ws ~f:(fun i w ->  x i == w)))) &&
  conj (List.mapi out_ws ~f:(fun i w -> x' i == w)) &&
  conj (List.map out_idxs ~f:(fun i -> ~! (u i)))

let enc_userdef ~in_ws ~out_ws ~is_commutative k j =
  let delta = List.length in_ws and alpha = List.length out_ws in
  let open Z3Ops in
  enc_semtc ~in_ws ~is_commutative ~out_ws ~alpha ~delta k j &&
  enc_prsv k j ~alpha ~delta && enc_sk_utlz k j ~alpha ~delta

let mk_userdef id ~in_ws ~out_ws ~opcode ~gas ~disasm ~is_commutative =
  mk ~id ~effect:(enc_userdef ~in_ws ~out_ws ~is_commutative) ~opcode ~gas ~disasm

(* predefined instructions *)

let mk_PUSH =
  mk ~id:"PUSH" ~opcode:"60" ~disasm:"PUSH" ~gas:3
    ~effect:(fun k j ->
      let a = mk_a j in
      enc_userdef ~in_ws:[] ~is_commutative:false ~out_ws:[a] k j
    )

let mk_POP =
  mk ~id:"POP" ~opcode:"50" ~gas:2 ~disasm:"POP"
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j in
        enc_userdef ~in_ws:[x_0] ~is_commutative:false ~out_ws:[] k j
      )

let mk_SWAP idx =
  let disasm = ("SWAP" ^ [%show: int] idx) in
  let opcode = hex_add "90" (idx-1) in
  mk ~id:disasm ~opcode ~disasm:disasm ~gas:3
    ~effect:(fun k j ->
        let x_0 = mk_x 0 j and x_l = mk_x idx j in
        let prsvd = List.map ~f:(fun i -> mk_x i j)
            (List.range ~start:`inclusive 1 ~stop:`exclusive idx) in
        enc_userdef ~in_ws:([x_0] @ prsvd @ [x_l]) ~is_commutative:false ~out_ws:([x_l] @ prsvd @ [x_0]) k j
      )

let mk_DUP idx =
  let disasm = ("DUP" ^ [%show: int] idx) in
  let opcode = hex_add "80" (idx-1) in
  mk ~id:disasm ~opcode:opcode ~disasm:disasm ~gas:3
    ~effect:(fun k j ->
        let x_idx = mk_x (idx-1) j in
        let prsvd = List.map ~f:(fun i -> mk_x i j)
            (List.range ~start:`inclusive 0 ~stop:`exclusive (idx-1)) in
        enc_userdef ~in_ws:(prsvd @ [x_idx]) ~is_commutative:false ~out_ws:([x_idx] @ prsvd @ [x_idx]) k j
      )

let mk_NOP =
  mk ~id:"NOP" ~opcode:"" ~disasm:"NOP" ~gas:0
    ~effect:(fun k j ->
        enc_userdef ~in_ws:[] ~is_commutative:false ~out_ws:[] k j
      )

let predef ~k =
  let max_idx = Int.min (k-1) 16 in
  [mk_PUSH; mk_POP; mk_NOP] @
  (List.map ~f:mk_SWAP (List.range ~start:`inclusive 1 ~stop:`inclusive max_idx)) @
  (List.map ~f:mk_DUP (List.range ~start:`inclusive 1 ~stop:`inclusive max_idx))
