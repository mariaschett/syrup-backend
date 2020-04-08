open Core
open OUnit2
open Syrup_backend
open Z3util
open Sk_util

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

    "Initializing us of empty stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [] in
        let c = sk_init k j vals in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [btm; btm; btm; btm]
          (List.map (Consts.us k j) ~f:(eval_const m))
      );

    "Initializing us of full stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3; num 4] in
        let c = sk_init k j vals in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; top]
          (List.map (Consts.us k j) ~f:(eval_const m))
      );

  ]


let utlz = [
    "Initial stack is all utilized">:: (fun _ ->
        let k = 3 in let l = k and i = 0 in
        let c = enc_sk_utlz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.map (Consts.us k i) ~f:(fun _ -> top))
          (List.map (Consts.us k i) ~f:(eval_const m))
      );

    "Initial stack contains one element">:: (fun _ ->
        let k = 4 and l = 1 and i = 0 in
        let c = enc_sk_utlz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (top :: (List.init (k-l) ~f:(fun _ -> btm)))
          (List.map (Consts.us k i) ~f:(eval_const m))
      );

    "Initial stack contains two elements">:: (fun _ ->
        let k = 4 in let l = 2 in
        let c = enc_sk_utlz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          ([top; top] @ (List.init (k-l) ~f:(fun _ -> btm)))
          (List.map (Consts.us k 0) ~f:(eval_const m))
      );
  ]

let prsv =
  [
    "All stack is preserved (NOP)">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let l = List.length vals in
        let alpha = 0 and delta = 0 in
        let c = sk_init k j vals in
        let c' = enc_prsv k j ~alpha ~delta and c'' = enc_sk_utlz k j ~alpha ~delta in
        let m = solve_model_exn [c; c'; c''] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map (Consts.x's l j) ~f:(eval_const m))
      );

    "Stack is preserved for adding and deleting two words">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals_prsv = [num 3; num 4;] in
        let vals_chng = [num 1; num 2;] in
        let alpha = 2 and delta = 2 in
        let c = sk_init k j (vals_chng @ vals_prsv) in
        let c' = enc_prsv k j ~alpha ~delta and c'' = enc_sk_utlz k j ~alpha ~delta in
        let m = solve_model_exn [c; c'; c''] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals_prsv
          (List.map [Consts.mk_x' 2 j; Consts.mk_x' 3 j] ~f:(eval_const m))
      );

    "Stack is preserved after adding one word">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let alpha = 1 and delta = 0 in
        let c = sk_init k j vals in
        let c' = enc_prsv k j ~alpha ~delta and c'' = enc_sk_utlz k j ~alpha ~delta in
        let m = solve_model_exn [c; c'; c''] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Consts.mk_x 2 (j+1); Consts.mk_x 3 (j+1)] ~f:(eval_const m))
      );

    "Stack is preserved after deleting one word">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let alpha = 0 and delta = 1 in
        let c = sk_init k j vals in
        let c' = enc_prsv k j ~alpha ~delta and c'' = enc_sk_utlz k j ~alpha ~delta in
        let m = solve_model_exn [c; c'; c''] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );
  ]

let suite = "suite" >::: init @ utlz @ prsv

let () =
  run_test_tt_main suite
