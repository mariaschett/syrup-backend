open Core
open OUnit2
open Opti
open Z3util

let us k j = List.init k ~f:(fun i -> Enc.mk_u i j)
let u's k j = List.init k ~f:(fun i -> Enc.mk_u i (j + 1))

let sk_utlz k j utzd =
  let open Z3Ops in
  conj (List.map2_exn (us k j) utzd ~f:(fun u uz -> u == uz))

let sk_utilz =
  [
    "An empty initial stack">:: (fun _ ->
        let k = 3 and l = 0 and i = 0 in
        let c = Enc.enc_sk_utilz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.map (us k i) ~f:(fun _ -> btm))
          (List.map (us k i) ~f:(eval_const m))
      );

    "Initial stack is all utilized">:: (fun _ ->
        let k = 3 in let l = k and i = 0 in
        let c = Enc.enc_sk_utilz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (List.map (us k i) ~f:(fun _ -> top))
          (List.map (us k i) ~f:(eval_const m))
      );

    "Initial stack contains one element">:: (fun _ ->
        let k = 4 and l = 1 and i = 0 in
        let c = Enc.enc_sk_utilz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          (top :: (List.init (k-l) ~f:(fun _ -> btm)))
          (List.map (us k i) ~f:(eval_const m))
      );

    "Initial stack contains two elements">:: (fun _ ->
        let k = 4 in let l = 2 in
        let c = Enc.enc_sk_utilz_init k l in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          ([top; top] @ (List.init (k-l) ~f:(fun _ -> btm)))
          (List.map (us k 0) ~f:(eval_const m))
      );

    "Utilization of stack remains unchanged">:: (fun _ ->
        let k = 4 and j = 2 in
        let utlzd = [top; top; btm; btm] in
        let c = sk_utlz k j utlzd in
        let c' = Enc.enc_sk_utilz_unchanged k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          utlzd
          (List.map (u's k j) ~f:(eval_const m))
      );

    "Utilization after one word is added to the stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let utlzd = [top; top; btm; btm] in
        let c = sk_utlz k j utlzd in
        let c' = Enc.enc_sk_utilz_add k j 1 in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "Utilization after two words are added to the stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let utlzd = [top; btm; btm; btm] in
        let c = sk_utlz k j utlzd in
        let c' = Enc.enc_sk_utilz_add k j 2 in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "Utilization after one word is removed from the stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let utlzd = [top; top; btm; btm] in
        let c = sk_utlz k j utlzd in
        let c' = Enc.enc_sk_utilz_rm k j 1 in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; btm; btm; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "Utilization after two words are removed from the stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let utlzd = [top; top; btm; btm] in
        let c = sk_utlz k j utlzd in
        let c' = Enc.enc_sk_utilz_rm k j 2 in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [btm; btm; btm; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "Utilization after one word is added and then removed">:: (fun _ ->
        let k = 4 and j = 2 in
        let utlzd = [top; top; btm; btm] in
        let c = sk_utlz k j utlzd in
        let c' = Enc.enc_sk_utilz_add k j 1 in
        let c'' = Enc.enc_sk_utilz_rm k (j+1) 1 in
        let m = solve_model_exn [c; c'; c''] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          utlzd
          (List.map (u's k (j+1)) ~f:(eval_const m))
      );
  ]

let xs l j = List.init l ~f:(fun i -> Enc.mk_x i j)
let x's l j = List.init l ~f:(fun i -> Enc.mk_x i (j+1))

let sk_init l j vals =
  let open Z3Ops in
  conj (List.map2_exn (xs l j) vals ~f:(fun x v -> x == v))

let sk_presv =
  [
    "Initializing stack works as expected">:: (fun _ ->
        let j = 2 in
        let vals = [num 1; num 2;] in
        let l = List.length vals in
        let c = sk_init l j vals in
        let m = solve_model_exn [c] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map (xs l j) ~f:(eval_const m))
      );

    "All stack is preserved">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let l = List.length vals in
        let c = sk_init l j vals in
        let c' = Enc.enc_pres_all_from k 0 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map (x's l j) ~f:(eval_const m))
      );

    "Stack is preserved after two elements">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals_pres = [num 3; num 4;] in
        let vals_chng = [num 1; num 2;] in
        let c = sk_init k j (vals_chng @ vals_pres) in
        let c' = Enc.enc_pres_all_from k 2 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals_pres
          (List.map [Enc.mk_x 2 (j+1); Enc.mk_x 3 (j+1)] ~f:(eval_const m))
      );

    "Stack is preserved moving one element up from index 1">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init (List.length vals) j vals in
        let c' = Enc.enc_pres_move_up_from k 1 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Enc.mk_x 2 (j+1); Enc.mk_x 3 (j+1)] ~f:(eval_const m))
      );

    "Stack is preserved moving one element down from index 0">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init (List.length vals) j vals in
        let c' = Enc.enc_pres_move_down k 0 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Enc.mk_x 0 (j+1); Enc.mk_x 1 (j+1)] ~f:(eval_const m))
      );
  ]

let suite = "suite" >::: (sk_utilz @ sk_presv)

let () =
  run_test_tt_main suite
