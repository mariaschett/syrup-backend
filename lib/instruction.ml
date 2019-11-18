open Core
open Z3util
open Consts
open Instruction_util

module User_instr = struct
  type t =
    | Block_192
  [@@deriving show {with_path = false}, enumerate]

  let alpha_delta = function
    | Block_192 -> (2,1)
end

module Predef_instr = struct
  type t =
    | PUSH
    | POP
    | SWAP
    | DUP
    | NOP
  [@@deriving show {with_path = false}, enumerate]

  let alpha_delta = function
    | PUSH -> (0,1)
    | POP -> (1,0)
    | SWAP -> (2,2)
    | DUP -> (1,2)
    | NOP -> (0,0)
end

type t =
  | PREDEF of Predef_instr.t
  | USERDEF of User_instr.t
[@@deriving show {with_path = false}, enumerate]

let alpha_delta = function
  | PREDEF instr -> Predef_instr.alpha_delta instr
  | USERDEF instr -> User_instr.alpha_delta instr

let diff iota =
  let (alpha, delta) = alpha_delta iota in
  (alpha - delta)

let alpha iota = alpha_delta iota |> Tuple.T2.get1

let delta iota = alpha_delta iota |> Tuple.T2.get2

(* effect *)

let enc_push k j =
  let x'_0 = mk_x' 0 j in
  let u_k = mk_u (k-1) j in
  let a = mk_a j in
  let diff = diff (PREDEF PUSH) and alpha = alpha (PREDEF PUSH) in
  let open Z3Ops in
  ~! u_k &&
  (x'_0 == a && enc_prsv k j diff alpha && enc_sk_utlz k j diff)

let enc_pop k j =
  let u_0 = mk_u 0 j in
  let diff = diff (PREDEF POP) and alpha = alpha (PREDEF POP) in
  let open Z3Ops in
  u_0 && (enc_prsv k j diff alpha && enc_sk_utlz k j diff)

let enc_swap k j =
  let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
  let x_1 = mk_x 1 j and x'_1 = mk_x' 1 j in
  let u_0 = mk_u 0 j and u_1 = mk_u 1 j in
  let diff = diff (PREDEF SWAP) and alpha = alpha (PREDEF SWAP) in
  let open Z3Ops in
  u_0 && u_1 &&
  ((x'_0 == x_1) && (x'_1 == x_0)) && enc_prsv k j diff alpha && enc_sk_utlz k j diff

let enc_dup k j =
  let x_0 = mk_x 0 j and x'_0 = mk_x' 0 j in
  let x'_1 = mk_x' 1 j in
  let u_0 = mk_u 0 j and u_l = mk_u (k-1) j in
  let diff = diff (PREDEF DUP) and alpha = alpha (PREDEF DUP) in
  let open Z3Ops in
  u_0 && ~! u_l &&
  ((x'_0 == x_0) && (x'_1 == x_0) && enc_prsv k j diff alpha && enc_sk_utlz k j diff)

let enc_nop k j =
  let diff = diff (PREDEF NOP) and alpha = alpha (PREDEF NOP) in
  let open Z3Ops in
  enc_prsv k j diff alpha  && enc_sk_utlz k j diff

let effect k enc_userdef iota j =
  match iota with
  | PREDEF PUSH -> enc_push k j
  | PREDEF POP -> enc_pop k j
  | PREDEF SWAP -> enc_swap k j
  | PREDEF DUP -> enc_dup k j
  | PREDEF NOP -> enc_nop k j
  | USERDEF Block_192 -> enc_userdef j
