open Core
open OUnit2
open Opti
open Z3util
open Consts
open Sk_util

let push =
  let enc_push = (Instruction.mk_PUSH).effect in [

    "forwards: PUSH word on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_push k j in
        let c_word = Consts.mk_x 0 (j+1) <==> num 42 in
        let m = solve_model_exn [c; c'; c_word] in
        assert_equal
        ~cmp:[%eq: Z3.Expr.t]
        ~printer:Z3.Expr.to_string
        (num 42)
        (eval_const m (Consts.mk_a j))
      );

    "forwards: PUSH preserves words">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_push k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map [Consts.mk_x' 1 j; Consts.mk_x' 2 j] ~f:(eval_const m))
      );

    "forwards: PUSH utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_push k j in
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
        let c = enc_push k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 42)
          (eval_const m (Consts.mk_a j))
      );

    "backwards: PUSH preserves words">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 42; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_push k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2]
          (List.map [Consts.mk_x 0 j] ~f:(eval_const m))
      );

    "backwards: PUSH utilization of stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_push k j in
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
        let c' = enc_push k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let pop = let enc_pop = (Instruction.mk_POP).effect in
  [
    "forwards: POP preserves words">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3] in
        let c = sk_init k j vals in
        let c' = enc_pop k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1);] ~f:(eval_const m))
      );

    "forwards: POP utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3] in
        let c = sk_init k j vals in
        let c' = enc_pop k j in
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
        let c = enc_pop k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3]
          (List.map [Consts.mk_x 1 j; Consts.mk_x 2 j;] ~f:(eval_const m))
      );

    "backwards: POP utilization of stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_pop k j in
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
        let c' = enc_pop k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let swap = let enc_swap = (Instruction.mk_SWAP).effect in
  [
    "forwards: SWAP word on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_swap k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 1]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );

    "forwards: SWAP preserves words">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_swap k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 3;]
          (List.map [Consts.mk_x 2 (j+1)] ~f:(eval_const m))
      );

    "forwards: SWAP utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_swap k j in
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
        let c = enc_swap k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 1]
          (List.map [Consts.mk_x 0 j; Consts.mk_x 1 j] ~f:(eval_const m))
      );

    "backwards: SWAP preserves words">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_swap k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 3;]
          (List.map [Consts.mk_x 2 j] ~f:(eval_const m))
      );

    "backwards: SWAP utilization of stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_swap k j in
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
        let c' = enc_swap k j in
        assert_bool "" (is_unsat [c; c'] )
      );

    "Cannot SWAP on emtpy stack">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [] in
        let c = sk_init k j vals in
        let c' = enc_swap k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let dup = let enc_dup = (Instruction.mk_DUP).effect in
  [
    "forwards: DUP word on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 21; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_dup k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 21; num 21]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );

    "forwards: DUP preserves words">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_dup k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2;]
          (List.map [Consts.mk_x 2 (j+1)] ~f:(eval_const m))
      );

    "forwards: DUP utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_dup k j in
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
        let c = enc_dup k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 21;]
          (List.map [Consts.mk_x 0 j] ~f:(eval_const m))
      );

    "backwards: DUP preserves words">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 21; num 21; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_dup k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2;]
          (List.map [Consts.mk_x 1 j] ~f:(eval_const m))
      );

    "backwards: DUP utilization of stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 21; num 21; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_dup k j in
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
        let c' = enc_dup k j in
        assert_bool "" (is_unsat [c; c'] )
      );

    "Cannot DUP on emtpy stack">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [] in
        let c = sk_init k j vals in
        let c' = enc_dup k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let nop = let enc_nop = (Instruction.mk_NOP).effect in
  [
    "forwards: NOP preserves words on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_nop k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );

    "forwards: NOP keeps utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_nop k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );
  ]

let block_192_add_1 =
  let s_1 = mk_s 1 (* =^= ADD_1 *) in
  let s_0 = mk_s 0 (* =^= input variable on stack *) in
  let mk_block_192 = Instruction.mk_userdef "ADD_1" ~in_ws:[s_0; num 1] ~out_ws:[s_1] ~gas:3 ~opcode:"01" in
  let enc_add_1 = mk_block_192.effect in
  [
    "forwards: ADD_1 puts s_1 on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 1;] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        let s_1 = Consts.mk_s 1 in
        let x'_0 = Consts.mk_x 0 j in
        let c_s_1 = let open Z3Ops in s_1 == num 42 && x'_0 == s_1 in
        let m = solve_model_exn [c; c'; c_s_1] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 42)
          (eval_const m x'_0)
      );

    "forwards: ADD_1 is not applicable">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        assert_bool "" (is_unsat [c; c'])
      );

    "forwards: ADD_1 modifies utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 1;] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; btm; btm; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "forwards: ADD_1 preserves stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 1; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 3)
          (eval_const m (Consts.mk_x' 1 j))
      );

    "backwards: ADD_1 sk_x and 1 on the stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let s_1 = Consts.mk_s 1 in
        let vals = [s_1] in
        let c' = sk_init k (j+1) vals in
        let c = enc_add_1 k j in
        let s_0 = Consts.mk_s 0 in
        let c_sk = let open Z3Ops in s_0 == num 42 in
        let m = solve_model_exn [c; c'; c_sk] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 42; num 1]
          (List.map [Consts.mk_x 0 j; Consts.mk_x 1 j] ~f:(eval_const m))
      );

    "backwards: ADD_1 modifies utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let s_1 = Consts.mk_s 1 in
        let vals = [s_1] in
        let c' = sk_init k (j+1) vals in
        let c = enc_add_1 k j in
        let m = solve_model_exn [c; c';] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (us k j) ~f:(eval_const m))
      );

    "backwards: ADD_1 preserves stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let s_1 = Consts.mk_s 1 in
        let vals = [s_1; num 3] in
        let c' = sk_init k (j+1) vals in
        let c = enc_add_1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 3)
          (eval_const m (Consts.mk_x 2 j))
      );
  ]

let suite = "suite" >::: push @ pop @ swap @ dup @ nop @ block_192_add_1

let () =
  run_test_tt_main suite
