open Core
open OUnit2
open Opti
open Z3util

let sk_init k j vals =
  let l = List.length vals in
  let open Z3Ops in
  conj (
    (List.mapi vals ~f:(fun i v -> (Consts.mk_x i j == v) && (Consts.mk_u i j == top))) @
    (List.map (List.range l k) ~f:(fun i -> (Consts.mk_u i j == btm)))
  )

let init = [
    "Initializing stack initializes xs">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let l = List.length vals in
        let c = sk_init k j vals in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map (Consts.xs l j) ~f:(eval_const m))
    );

    "Initializing stack initializes us">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (Consts.us k j) ~f:(eval_const m))
      );
  ]

let suite = "suite" >::: (init)

let () =
  run_test_tt_main suite
