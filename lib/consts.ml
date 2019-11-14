open Core

(* program counter *)
type pc = int [@@deriving show {with_path = false}]

(* stack index *)
type si = int [@@deriving show {with_path = false}]

(* stack utilization u at stack index i after j instructions *)
let mk_u (i : si) (j : pc) =
  Z3util.boolconst ("u_" ^ [%show: pc] i ^ "_" ^ [%show: si] j)
let mk_u' (i : si) (j : pc) = mk_u i (j+1)

(* words on stack are modeled as integer *)
(* word x at stack index i after executing j instructions *)
let mk_x (i : si) (j : pc) =
  Z3util.intconst ("x_" ^ [%show: pc] i ^ "_" ^ [%show: si] j)
(* argument a of instruction after j instructions *)
let mk_a (j : pc) = Z3util.intconst ("a_" ^ [%show: pc] j)

(* instructions are modeled as integers *)
(* template t to assign instructions *)
let mk_t (j : pc) = Z3util.intconst ("t_" ^ [%show: pc] j)

(* words on the final stack *)
let mk_s (j : pc) = Z3util.intconst ("s_" ^ [%show: int] j)
