(*   Copyright 2020 Maria A Schett

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
