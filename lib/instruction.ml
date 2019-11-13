open Core

type t =
    SWAP
  | PUSH
  | ADD
  | POP
  | DUP
  | NOP
[@@deriving show {with_path = false}, enumerate]

let enc iota =
  let i =
    match iota with
    | SWAP -> 0
    | PUSH -> 1
    | ADD -> 2
    | POP -> 3
    | DUP -> 4
    | NOP -> 5
  in Z3util.num i

let alpha_delta = function
  | SWAP -> (2,2)
  | PUSH -> (0,1)
  | ADD -> (2,1)
  | POP -> (1,0)
  | DUP -> (1,2)
  | NOP -> (0,0)

let diff iota =
  let (alpha, delta) = alpha_delta iota in
  (alpha - delta)

let alpha iota = alpha_delta iota |> Tuple.T2.get1

let delta iota = alpha_delta iota |> Tuple.T2.get2
