open Core
open OUnit2
open Opti
open Z3util

let xs l j = List.init l ~f:(fun i -> Consts.mk_x i j)
let x's l j = List.init l ~f:(fun i -> Consts.mk_x i (j+1))

let us k j = List.init k ~f:(fun i -> Consts.mk_u i j)

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
          (List.map (xs l j) ~f:(eval_const m))
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
          (List.map (us k j) ~f:(eval_const m))
      );
]

let prsv =
  [
    "All stack is preserved">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let l = List.length vals in
        let c = sk_init k j vals in
        let c' = Enc.enc_prsv_from_diff 0 k 0 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map (x's l j) ~f:(eval_const m))
      );

    "Stack is preserved after index 2">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals_prsv = [num 3; num 4;] in
        let vals_chng = [num 1; num 2;] in
        let c = sk_init k j (vals_chng @ vals_prsv) in
        let c' = Enc.enc_prsv_from_diff 0 k 2 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals_prsv
          (List.map [Consts.mk_x 2 (j+1); Consts.mk_x 3 (j+1)] ~f:(eval_const m))
      );

    "Stack is preserved after moving one element up from index 1">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = Enc.enc_prsv_from_diff (-1) k 1 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Consts.mk_x 2 (j+1); Consts.mk_x 3 (j+1)] ~f:(eval_const m))
      );

    "Stack is preserved after moving one element down from index 0">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = Enc.enc_prsv_from_diff 1 k 0 j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );
  ]

let suite = "suite" >::: (init @ prsv)

let () =
  run_test_tt_main suite
