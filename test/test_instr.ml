open Core
open OUnit2
open Opti
open Z3util

let xs l j = List.init l ~f:(fun i -> Enc.mk_x i j)
let x's l j = List.init l ~f:(fun i -> Enc.mk_x i (j+1))

let us k j = List.init k ~f:(fun i -> Enc.mk_u i j)
let u's k j = List.init k ~f:(fun i -> Enc.mk_u i (j+1))

let sk_init k j vals =
  let l = List.length vals in
  let open Z3Ops in
  conj (
    (List.mapi vals ~f:(fun i v -> (Enc.mk_x i j == v) && (Enc.mk_u i j == top))) @
    (List.map (List.range l k) ~f:(fun i -> (Enc.mk_u i j == btm)))
  )

let push = [

  "forwards: PUSH word on stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_push k j in
      let c_word = Enc.mk_x 0 (j+1) <==> num 42 in
      let m = solve_model_exn [c; c'; c_word] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t]
        ~printer:Z3.Expr.to_string
        (num 42)
        (eval_const m (Enc.mk_a j))
    );

  "forwards: PUSH preserves words">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_push k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        vals
        (List.map [Enc.mk_x 1 (j+1); Enc.mk_x 2 (j+1)] ~f:(eval_const m))
    );

  "forwards: PUSH utilization of stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_push k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
    );

  "backwards: PUSH word on stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 42; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_push k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t]
        ~printer:Z3.Expr.to_string
        (num 42)
        (eval_const m (Enc.mk_a j))
    );

  "backwards: PUSH preserves words">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 42; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_push k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2]
        (List.map [Enc.mk_x 0 j] ~f:(eval_const m))
    );

  "backwards: PUSH utilization of stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 1; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_push k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; btm; btm; btm]
          (List.map (us k j) ~f:(eval_const m))
    );

  "Cannot PUSH on fully utilized stack">:: (fun _ ->
      let k = 3 and j = 0 in
      let vals = [num 1; num 2; num 1;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_push k j in
      assert_bool "" (is_unsat [c; c'] )
    );
]

let pop = [

  "forwards: POP preserves words">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2; num 3] in
      let c = sk_init k j vals in
      let c' = Enc.enc_pop k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2; num 3]
        (List.map [Enc.mk_x 0 (j+1); Enc.mk_x 1 (j+1);] ~f:(eval_const m))
    );

  "forwards: POP utilization of stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2; num 3] in
      let c = sk_init k j vals in
      let c' = Enc.enc_pop k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (u's k j) ~f:(eval_const m))
    );

  "backwards: POP preserves words">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 2; num 3] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_pop k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2; num 3]
        (List.map [Enc.mk_x 1 j; Enc.mk_x 2 j;] ~f:(eval_const m))
    );

  "backwards: POP utilization of stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 1; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_pop k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (us k j) ~f:(eval_const m))
    );

  "Cannot POP from emtpy stack">:: (fun _ ->
      let k = 3 and j = 0 in
      let vals = [] in
      let c = sk_init k j vals in
      let c' = Enc.enc_pop k j in
      assert_bool "" (is_unsat [c; c'] )
    );
  ]

let swap = [

  "forwards: SWAP word on stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2; num 3;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_swap k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2; num 1]
        (List.map [Enc.mk_x 0 (j+1); Enc.mk_x 1 (j+1)] ~f:(eval_const m))
    );

  "forwards: SWAP preserves words">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2; num 3;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_swap k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 3;]
        (List.map [Enc.mk_x 2 (j+1)] ~f:(eval_const m))
    );

  "forwards: SWAP utilization of stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2; num 3;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_swap k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
    );

  "backwards: SWAP word on stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 1; num 2; num 3;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_swap k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2; num 1]
        (List.map [Enc.mk_x 0 j; Enc.mk_x 1 j] ~f:(eval_const m))
    );

  "backwards: SWAP preserves words">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 1; num 2; num 3;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_swap k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 3;]
        (List.map [Enc.mk_x 2 j] ~f:(eval_const m))
    );

  "backwards: SWAP utilization of stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 1; num 2; num 3;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_swap k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (us k j) ~f:(eval_const m))
    );

  "Cannot SWAP on stack with only 1 word">:: (fun _ ->
      let k = 3 and j = 0 in
      let vals = [num 3] in
      let c = sk_init k j vals in
      let c' = Enc.enc_swap k j in
      assert_bool "" (is_unsat [c; c'] )
    );

  "Cannot SWAP on emtpy stack">:: (fun _ ->
      let k = 3 and j = 0 in
      let vals = [] in
      let c = sk_init k j vals in
      let c' = Enc.enc_swap k j in
      assert_bool "" (is_unsat [c; c'] )
    );
]

let dup = [

  "forwards: DUP word on stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 21; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_dup k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 21; num 21]
        (List.map [Enc.mk_x 0 (j+1); Enc.mk_x 1 (j+1)] ~f:(eval_const m))
    );

  "forwards: DUP preserves words">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_dup k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2;]
        (List.map [Enc.mk_x 2 (j+1)] ~f:(eval_const m))
    );

  "forwards: DUP utilization of stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_dup k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
    );

  "backwards: DUP word on stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 21; num 21; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_dup k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 21;]
        (List.map [Enc.mk_x 0 j] ~f:(eval_const m))
    );

  "backwards: DUP preserves words">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 21; num 21; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_dup k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        [num 2;]
        (List.map [Enc.mk_x 1 j] ~f:(eval_const m))
    );

  "backwards: DUP utilization of stack">:: (fun _ ->
      let k = 4 and j = 2 in
      let vals = [num 21; num 21; num 2;] in
      let c' = sk_init k (j+1) vals in
      let c = Enc.enc_dup k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (us k j) ~f:(eval_const m))
    );

  "Cannot DUP on full stack">:: (fun _ ->
      let k = 3 and j = 0 in
      let vals = [num 3; num 2; num 3] in
      let c = sk_init k j vals in
      let c' = Enc.enc_dup k j in
      assert_bool "" (is_unsat [c; c'] )
    );

  "Cannot DUP on emtpy stack">:: (fun _ ->
      let k = 3 and j = 0 in
      let vals = [] in
      let c = sk_init k j vals in
      let c' = Enc.enc_dup k j in
      assert_bool "" (is_unsat [c; c'] )
    );
]

let nop = [

  "forwards: NOP preserves words on stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_nop k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
        vals
        (List.map [Enc.mk_x 0 (j+1); Enc.mk_x 1 (j+1)] ~f:(eval_const m))
    );

  "forwards: NOP keeps utilization of stack">:: (fun _ ->
      let k = 4 and j = 0 in
      let vals = [num 1; num 2;] in
      let c = sk_init k j vals in
      let c' = Enc.enc_nop k j in
      let m = solve_model_exn [c; c'] in
      assert_equal
        ~cmp:[%eq: Z3.Expr.t list]
        ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (u's k j) ~f:(eval_const m))
    );
]

let suite = "suite" >::: push @ pop @ swap @ dup @ nop

let () =
  run_test_tt_main suite
