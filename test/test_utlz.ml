open Core
open OUnit2
open Opti
open Z3util
open Test_util

let utlz = [
    "Initial stack is all utilized">:: (fun _ ->
        let k = 3 in let l = k and i = 0 in
        let c = Enc.enc_sk_utlz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.map (us k i) ~f:(fun _ -> top))
          (List.map (us k i) ~f:(eval_const m))
      );

    "Initial stack contains one element">:: (fun _ ->
        let k = 4 and l = 1 and i = 0 in
        let c = Enc.enc_sk_utlz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (top :: (List.init (k-l) ~f:(fun _ -> btm)))
          (List.map (us k i) ~f:(eval_const m))
      );

    "Initial stack contains two elements">:: (fun _ ->
        let k = 4 in let l = 2 in
        let c = Enc.enc_sk_utlz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          ([top; top] @ (List.init (k-l) ~f:(fun _ -> btm)))
          (List.map (us k 0) ~f:(eval_const m))
      );

  ]

let suite = "suite" >::: utlz

let () =
  run_test_tt_main suite
