open Auxtest

let%expect_test "stlc/stlc" =
  run_test "data/PLDI23/stlc/stlc.ml";
  [%expect
    {|
    passing: type_eq, gen_const, gen_type_size, gen_type, vars_with_type_rev_index, vars_with_type, gen_term_no_app, gen_term_size
    failing:
  |}]

let%expect_test "leonidas/SizedBST" =
  run_test "data/PLDI23/leonidas/SizedBST.ml";
  [%expect {|
    passing: size_bst_gen
    failing:
  |}]

let%expect_test "elrond/LeftistHeap" =
  run_test "data/PLDI23/elrond/LeftistHeap.ml";
  [%expect {|
    passing: leftisthp_gen
    failing:
  |}]

let%expect_test "quickcheck/SizedSet" =
  run_test "data/PLDI23/quickcheck/SizedSet.ml";
  [%expect {|
    passing: ranged_set_gen
    failing:
  |}]
