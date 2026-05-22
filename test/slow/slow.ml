open Auxtest

let%expect_test "quickchick/SortedList" =
  run_test "data/PLDI23/quickchick/SortedList.ml";
  [%expect {|
    passing: sorted_list_gen
    failing:
  |}]
