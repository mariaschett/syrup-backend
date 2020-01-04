open Core

let rec permutations xs0 =
  let rec perms xs is = match xs with
    | [] -> []
    | (t :: ts) ->
      let rec interleave' f xs' r = match xs' with
        | [] -> (ts, r)
        | (y :: ys) ->
          let (us, zs) = interleave' (fun xs -> f (List.cons y xs)) ys r in
          (y :: us, f (t :: y :: us) :: zs)
      in
      let interleave xs r = let (_, zs) = interleave' Fn.id xs r in zs in
      List.fold_right (permutations is) ~f:interleave ~init:(perms ts (t :: is))
  in
  xs0 :: perms xs0 []
