open Core
open Z3util
open Consts

(* stack utilization *)

let enc_sk_utlz_init k l =
  let u i = mk_u i 0 in
  let is_utlzd i =  if i < l then top else btm in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u i == is_utlzd i))

let enc_sk_utlz_shft k j diff =
  let u' i = mk_u' i j in
  let u i = mk_u i j in
  let shft i =
    if diff >= 0
    then if i < diff then top else u (i-diff)
    else if i > k - (abs(diff)) then btm else u (i+(abs(diff)))
  in
  let open Z3Ops in
  conj (List.init k ~f:(fun i -> u' i == shft i))

let enc_sk_utlz k j diff = enc_sk_utlz_shft k j diff

(* preserve *)

let enc_prsv_from_diff k j diff l =
  let u' i = mk_u' i j in
  let x i = mk_x (i-diff) j and x' i = mk_x' i j in
  let ks = List.range l k in
  let open Z3Ops in
  conj (List.map ks ~f:(fun i -> u' i ==> (x' i == x i)))

let enc_prsv k j diff alpha =
  enc_prsv_from_diff k j diff alpha
