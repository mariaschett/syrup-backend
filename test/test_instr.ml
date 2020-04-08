open Core
open OUnit2
open Syrup_backend
open Z3util
open Consts
open Instruction
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

let swap1 =
  let enc_swap1 = (Instruction.mk_SWAP 1).effect in
  [
    "forwards: SWAP1 word on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_swap1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 1]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );

    "forwards: SWAP1 preserves words">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_swap1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 3;]
          (List.map [Consts.mk_x 2 (j+1)] ~f:(eval_const m))
      );

    "forwards: SWAP1 utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3;] in
        let c = sk_init k j vals in
        let c' = enc_swap1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "backwards: SWAP1 word on stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_swap1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 1]
          (List.map [Consts.mk_x 0 j; Consts.mk_x 1 j] ~f:(eval_const m))
      );

    "backwards: SWAP1 preserves words">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_swap1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 3;]
          (List.map [Consts.mk_x 2 j] ~f:(eval_const m))
      );

    "backwards: SWAP1 utilization of stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_swap1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (us k j) ~f:(eval_const m))
      );

    "Cannot SWAP1 on stack with only 1 word">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [num 3] in
        let c = sk_init k j vals in
        let c' = enc_swap1 k j in
        assert_bool "" (is_unsat [c; c'] )
      );

    "Cannot SWAP1 on emtpy stack">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [] in
        let c = sk_init k j vals in
        let c' = enc_swap1 k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let swap3 =
  let enc_swap3 = (Instruction.mk_SWAP 3).effect in
  [
    "forwards: SWAP3 word on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3; num 4;] in
        let c = sk_init k j vals in
        let c' = enc_swap3 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 4; num 1;]
          (List.map [Consts.mk_x' 0 j; Consts.mk_x' 3 j] ~f:(eval_const m))
      );

    "forwards: SWAP3 preserves words within SWAP range">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2; num 3; num 4;] in
        let c = sk_init k j vals in
        let c' = enc_swap3 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2; num 3;]
          (List.map [Consts.mk_x' 1 j; Consts.mk_x' 2 j] ~f:(eval_const m))
      );

    "forwards: SWAP3 preserves words out of range">:: (fun _ ->
        let k = 5 and j = 0 in
        let vals = [num 1; num 2; num 3; num 4; num 5] in
        let c = sk_init k j vals in
        let c' = enc_swap3 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 5;]
          (List.map [Consts.mk_x' 4 j] ~f:(eval_const m))
      );

    "forwards: SWAP3 utilization of stack">:: (fun _ ->
        let k = 5 and j = 0 in
        let vals = [num 1; num 2; num 3; num 4;] in
        let c = sk_init k j vals in
        let c' = enc_swap3 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "backwards: SWAP3 word on stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 1; num 2; num 3; num 4;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_swap3 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 4; num 1]
          (List.map [Consts.mk_x 0 j; Consts.mk_x 3 j] ~f:(eval_const m))
      );

    "Cannot SWAP3 on stack with only 2 words">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [num 3; num 4] in
        let c = sk_init k j vals in
        let c' = enc_swap3 k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let dup1 = let enc_dup1 = (Instruction.mk_DUP 1).effect in
  [
    "forwards: DUP1 word on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 21; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_dup1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 21; num 21]
          (List.map [Consts.mk_x 0 (j+1); Consts.mk_x 1 (j+1)] ~f:(eval_const m))
      );

    "forwards: DUP1 preserves words">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_dup1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2;]
          (List.map [Consts.mk_x 2 (j+1)] ~f:(eval_const m))
      );

    "forwards: DUP1 utilization of stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [num 1; num 2;] in
        let c = sk_init k j vals in
        let c' = enc_dup1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; top; btm]
          (List.map (u's k j) ~f:(eval_const m))
      );

    "backwards: DUP1 word on stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 21; num 21; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_dup1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 21;]
          (List.map [Consts.mk_x 0 j] ~f:(eval_const m))
      );

    "backwards: DUP1 preserves words">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 21; num 21; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_dup1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 2;]
          (List.map [Consts.mk_x 1 j] ~f:(eval_const m))
      );

    "backwards: DUP1 utilization of stack">:: (fun _ ->
        let k = 4 and j = 2 in
        let vals = [num 21; num 21; num 2;] in
        let c' = sk_init k (j+1) vals in
        let c = enc_dup1 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [top; top; btm; btm]
          (List.map (us k j) ~f:(eval_const m))
      );

    "Cannot DUP1 on full stack">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [num 3; num 2; num 3] in
        let c = sk_init k j vals in
        let c' = enc_dup1 k j in
        assert_bool "" (is_unsat [c; c'] )
      );

    "Cannot DUP1 on emtpy stack">:: (fun _ ->
        let k = 3 and j = 0 in
        let vals = [] in
        let c = sk_init k j vals in
        let c' = enc_dup1 k j in
        assert_bool "" (is_unsat [c; c'] )
      );
  ]

let dup10 = let enc_dup10 = (Instruction.mk_DUP 10).effect in
  [
    "forwards: DUP10 word on stack">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = List.init 10 ~f:(fun i -> num (i+1)) in
        let c = sk_init k j vals in
        let c' = enc_dup10 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 10; num 10]
          (List.map [Consts.mk_x' 0 j; Consts.mk_x' 10 j] ~f:(eval_const m))
      );

    "forwards: DUP10 preserves words within range of DUP">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = List.init 10 ~f:(fun i -> num (i+1)) in
        let c = sk_init k j vals in
        let c' = enc_dup10 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          vals
          (List.map (List.mapi vals ~f:(fun i _ -> Consts.mk_x' (i+1) j)) ~f:(eval_const m))
      );

    "forwards: DUP10 preserves words out of range of DUP">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = (List.init 10 ~f:(fun i -> num (i+1))) @ [num 42] in
        let c = sk_init k j vals in
        let c' = enc_dup10 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 42;]
          (List.map [Consts.mk_x' 11 j] ~f:(eval_const m))
      );

    "forwards: DUP10 utilization of stack">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = List.init 10 ~f:(fun i -> num (i+1)) in
        let c = sk_init k j vals in
        let c' = enc_dup10 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          ((List.init 10 ~f:(fun _ -> top)) @ [top; btm])
          (List.map (u's k j) ~f:(eval_const m))
      );

    "backwards: DUP10 word on stack">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = [num 42; num 2; num 3; num 4; num 5; num 6; num 7; num 8; num 9; num 10; num 42] in
        let c' = sk_init k (j+1) vals in
        let c = enc_dup10 k j in
        let m = solve_model_exn [c; c'] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t list]
          ~printer:(List.to_string ~f:Z3.Expr.to_string)
          [num 42;]
          (List.map [Consts.mk_x 9 j] ~f:(eval_const m))
      );

    "Cannot DUP1 on full stack">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = List.init 12 ~f:(fun i -> num (i+1)) in
        let c = sk_init k j vals in
        let c' = enc_dup10 k j in
        assert_bool "" (is_unsat [c; c'] )
      );

    "Cannot DUP10 on stack with 9 words">:: (fun _ ->
        let k = 12 and j = 0 in
        let vals = List.init 9 ~f:(fun i -> num (i+1)) in
        let c = sk_init k j vals in
        let c' = enc_dup10 k j in
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
  let s_1 = mk_user_const "s_1" (* =^= ADD_1 *) in
  let s_0 = mk_user_const "s_0" (* =^= input variable on stack *) in
  let mk_block_192 = Instruction.mk_userdef "ADD_1" ~in_ws:[s_0; num 1] ~is_commutative:false ~out_ws:[s_1] ~gas:3 ~opcode:"01" ~disasm:"ADD" in
  let enc_add_1 = mk_block_192.effect in
  [
    "forwards: ADD_1 puts s_1 on stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 1] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        let x'_0 = Consts.mk_x' 0 j in
        let c_s_1 = let open Z3Ops in s_1 == num 42 in
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
        let vals = [s_1] in
        let c' = sk_init k (j+1) vals in
        let c = enc_add_1 k j in
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

let callvalue = [
  let s_0 = mk_user_const "s_0" in
  let mk_callvalue = Instruction.mk_userdef "CALLVALUE_1" ~in_ws:[] ~is_commutative:false ~out_ws:[s_0] ~gas:2 ~opcode:"34" ~disasm:"CALLVALUE" in
  let enc_callvalue = mk_callvalue.effect in

  "forwards: put callvalue on the stack">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [] in
        let c = sk_init k j vals in
        let c' = enc_callvalue k j in
        let x'_0 = Consts.mk_x' 0 j in
        let c_sk = let open Z3Ops in s_0 == num 42 in
        let m = solve_model_exn [c; c'; c_sk] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 42)
          (eval_const m x'_0)
      );
]

let block_commutative =
  let s_1 = mk_user_const "s_1" (* =^= ADD_1 *) in
  let s_0 = mk_user_const "s_0" (* =^= input variable on stack *) in
  let mk_block_commutative = Instruction.mk_userdef "ADD_1" ~in_ws:[s_0; num 1] ~is_commutative:true ~out_ws:[s_1] ~gas:3 ~opcode:"01" ~disasm:"ADD" in
  let enc_add_1 = mk_block_commutative.effect in
  [
    "forwards: ADD_1 puts s_1 on stack for [s_0; 1]">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 1] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        let x'_0 = Consts.mk_x' 0 j in
        let c_s_1 = let open Z3Ops in s_1 == num 42 in
        let m = solve_model_exn [c; c'; c_s_1] in
        assert_equal
          ~cmp:[%eq: Z3.Expr.t]
          ~printer:Z3.Expr.to_string
          (num 42)
          (eval_const m x'_0)
      );

    "forwards: ADD_1 puts s_1 on stack for [1; s_0]">:: (fun _ ->
        let k = 4 and j = 0 in
        let vals = [s_0; num 1] in
        let c = sk_init k j vals in
        let c' = enc_add_1 k j in
        let x'_0 = Consts.mk_x' 0 j in
        let c_s_1 = let open Z3Ops in s_1 == num 42 in
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

]

let suite = "suite" >:::
            push @ pop @ swap1 @ swap3
            @ dup1 @ dup10 @ nop @ block_192_add_1 @ callvalue @ block_commutative

let () =
  run_test_tt_main suite
