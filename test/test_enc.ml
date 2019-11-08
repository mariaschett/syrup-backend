open Core
open OUnit2
open Opti
open Z3util

let sk_utilz =
  [

    "Initial stack is all empty">:: (fun _ ->
        let k = 3 and l = 0 in
        let c = Enc.enc_sc_init k l in
        let m = solve_model_exn [c] in
        let us = List.init k ~f:(fun i -> Enc.mk_u i 0) in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init k ~f:(fun _ -> btm)) (List.map us ~f:(eval_const m))
      );

    "Initial stack is all utilized">:: (fun _ ->
        let k = 3 in let l = k in
        let c = Enc.enc_sc_init k l in
        let m = solve_model_exn [c] in
        let us = List.init k ~f:(fun i -> Enc.mk_u i 0) in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.init k ~f:(fun _ -> top)) (List.map us ~f:(eval_const m))
      );
  ]

let suite = "suite" >::: sk_utilz

let () =
  run_test_tt_main suite
