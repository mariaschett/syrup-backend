(*   Copyright 2020 Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Core

(* program counter *)
type pc = int [@@deriving show {with_path = false}]

(* stack index *)
type si = int [@@deriving show {with_path = false}]

(* consts given by user *)
type user_const = string [@@deriving show {with_path = false}, yojson]

(* stack utilization u at stack index i after j instructions *)
let mk_u (i : si) (j : pc) =
  Z3util.boolconst ("u_" ^ [%show: pc] i ^ "_" ^ [%show: si] j)
let mk_u' (i : si) (j : pc) = mk_u i (j+1)

(* words on stack are modeled as integer *)
(* word x at stack index i after executing j instructions *)
let mk_x (i : si) (j : pc) =
  Z3util.intconst ("x_" ^ [%show: pc] i ^ "_" ^ [%show: si] j)
let mk_x' (i : si) (j : pc) = mk_x i (j+1)
(* argument a of instruction after j instructions *)
let mk_a (j : pc) = Z3util.intconst ("a_" ^ [%show: pc] j)

(* instructions are modeled as integers *)
(* template t to assign instructions *)
let mk_t (j : pc) = Z3util.intconst ("t_" ^ [%show: pc] j)

let mk_user_const (c : user_const) = Z3util.intconst c

let xs l j = List.init l ~f:(fun i -> mk_x i j)
let x's l j = List.init l ~f:(fun i -> mk_x' i j)

let us k j = List.init k ~f:(fun i -> mk_u i j)
let u's k j = List.init k ~f:(fun i -> mk_u' i j)
