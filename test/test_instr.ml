open Core
open OUnit2
open Opti
open Z3util

let xs l j = List.init l ~f:(fun i -> Enc.mk_x i j)
let x's l j = List.init l ~f:(fun i -> Enc.mk_x i (j+1))

let us l j = List.init l ~f:(fun i -> Enc.mk_x i j)

let sk_init j vals =
  let open Z3Ops in
  conj (List.mapi vals ~f:(fun i v -> (Enc.mk_x i j == v) && (Enc.mk_u i j == top)))

let push = [

  ]

let suite = "suite" >::: push

let () =
  run_test_tt_main suite
