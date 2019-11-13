open Core

module User_instr = struct
  type t =
    | Block_192
  [@@deriving show {with_path = false}, enumerate]

  let enc = function
    | Block_192 -> 6

  let alpha_delta = function
    | Block_192 -> (2,1)
end

type t =
    SWAP
  | PUSH
  | POP
  | DUP
  | NOP
  | USERDEF of User_instr.t
[@@deriving show {with_path = false}, enumerate]

let enc iota =
  let i =
    match iota with
    | SWAP -> 0
    | PUSH -> 1
    | POP -> 2
    | DUP -> 3
    | NOP -> 4
    | USERDEF instr -> User_instr.enc instr
  in Z3util.num i

let alpha_delta = function
  | SWAP -> (2,2)
  | PUSH -> (0,1)
  | POP -> (1,0)
  | DUP -> (1,2)
  | NOP -> (0,0)
  | USERDEF instr -> User_instr.alpha_delta instr

let diff iota =
  let (alpha, delta) = alpha_delta iota in
  (alpha - delta)

let alpha iota = alpha_delta iota |> Tuple.T2.get1

let delta iota = alpha_delta iota |> Tuple.T2.get2
