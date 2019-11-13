
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
