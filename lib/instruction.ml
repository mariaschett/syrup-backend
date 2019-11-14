open Core

module User_instr = struct
  type t =
    | Block_192
  [@@deriving show {with_path = false}, enumerate]

  let enc = function
    | Block_192 -> Z3util.num 5

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

  let enc iota =
    let i =
      match iota with
      | PUSH -> 1
      | POP -> 2
      | SWAP -> 0
      | DUP -> 3
      | NOP -> 4
    in Z3util.num i

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

let enc = function
  | PREDEF instr -> Predef_instr.enc instr
  | USERDEF instr -> User_instr.enc instr

let alpha_delta = function
  | PREDEF instr -> Predef_instr.alpha_delta instr
  | USERDEF instr -> User_instr.alpha_delta instr

let diff iota =
  let (alpha, delta) = alpha_delta iota in
  (alpha - delta)

let alpha iota = alpha_delta iota |> Tuple.T2.get1

let delta iota = alpha_delta iota |> Tuple.T2.get2
