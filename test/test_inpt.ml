open OUnit2

let inpt = [

  ]

let suite = "suite" >::: inpt

let () =
  run_test_tt_main suite
