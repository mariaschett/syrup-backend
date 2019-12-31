open Core
open Z3util
open Consts

let sk_init k j vals =
  let l = List.length vals in
  let open Z3Ops in
  conj (
    (List.mapi vals ~f:(fun i v -> (Consts.mk_x i j == v) && (Consts.mk_u i j == top))) @
    (List.map (List.range l k) ~f:(fun i -> (Consts.mk_u i j == btm)))
  )

(* stack utilization *)

let enc_sk_utlz_init k l =
  let u i = mk_u i 0 in
  let is_utlzd i =  if i < l then top else btm in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u i == is_utlzd i))

let idx_to_add alpha =
  List.range ~start:`inclusive 0 ~stop:`exclusive alpha

let idx_to_del k alpha delta =
  List.range ~start:`inclusive (k-delta+alpha) ~stop:`exclusive k

let idxs_to_shift k alpha delta =
  (* to avoid generating x_l_j for l >= k *)
  let k = if alpha > delta then k - alpha + delta else k in
  List.range ~start:`inclusive delta ~stop:`exclusive k

let enc_sk_utlz_add j ~alpha =
  let u' i = mk_u' i j in
  let open Z3Ops in
  conj (List.map (idx_to_add alpha) ~f:(fun i -> u' i == top))

let enc_sk_utlz_prsv k j ~alpha ~delta =
  let u i = mk_u i j and u' i = mk_u' (i-delta+alpha) j in
  let open Z3Ops in
  conj (List.map (idxs_to_shift k alpha delta) ~f:(fun i -> u' i == u i))

let enc_sk_utlz_del k j ~alpha ~delta =
  let u' i = mk_u' i j in
  let open Z3Ops in
  conj (List.map (idx_to_del k alpha delta) ~f:(fun i -> u' i == btm))

let enc_sk_utlz k j ~alpha ~delta =
  let open Z3Ops in
  enc_sk_utlz_add j ~alpha &&
  enc_sk_utlz_prsv k j ~alpha ~delta &&
  enc_sk_utlz_del k j ~alpha ~delta

(* preserve *)

let enc_prsv k j ~alpha ~delta =
  let u i = mk_u i j in
  let x i = mk_x i j and x' i = mk_x' (i-delta+alpha) j in
  let idx = idxs_to_shift k alpha delta in
  let open Z3Ops in
  conj (List.map idx ~f:(fun i -> u i ==> (x' i == x i)))
