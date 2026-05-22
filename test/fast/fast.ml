open Auxtest

let%expect_test "inline_test/alias" =
  run_test "data/inline_test/alias.ml";
  [%expect {|
    passing:
    failing:
  |}]

let%expect_test "test_cases/basic_int" =
  run_test "data/test_cases/basic_int.ml";
  [%expect {|
    passing: test1 
    failing: test3 
  |}]

let%expect_test "basic/duplicate_list" =
  run_test "data/PLDI23/basic/duplicate_list.ml";
  [%expect {|
    passing: duplicate_list_gen 
    failing:
  |}]

let%expect_test "basic/sortedlist_simpl" =
  run_test "data/PLDI23/basic/sortedlist_simpl.ml";
  [%expect {|
    passing: sorted_list_gen 
    failing:
  |}]

let%expect_test "basic/boundlist" =
  run_test "data/PLDI23/basic/boundlist.ml";
  [%expect {|
    passing: bound_list_gen 
    failing:
  |}]

let%expect_test "quickchick/SizedTree" =
  run_test "data/PLDI23/quickchick/SizedTree.ml";
  [%expect {|
    passing: depth_tree_gen
    failing:
  |}]

let%expect_test "quickchick/RedBlackTree" =
  run_test "data/PLDI23/quickchick/RedBlackTree.ml";
  [%expect {|
    passing: rbtree_gen
    failing:
  |}]

let%expect_test "quickchick/SizedList" =
  run_test "data/PLDI23/quickchick/SizedList.ml";
  [%expect {|
    passing: sized_list_gen
    failing:
  |}]

let%expect_test "leonidas/CompleteTree" =
  run_test "data/PLDI23/leonidas/CompleteTree.ml";
  [%expect {|
    passing: complete_tree_gen
    failing:
  |}]

let%expect_test "elrond/UniqueList" =
  run_test "data/PLDI23/elrond/UniqueList.ml";
  [%expect {|
    passing: unique_list_gen
    failing:
  |}]

let%expect_test "elrond/BatchedQueue" =
  run_test "data/PLDI23/elrond/BatchedQueue.ml";
  [%expect {|
    passing: batchedq_gen
    failing:
  |}]

let%expect_test "elrond/UnbalanceSet" =
  run_test "data/PLDI23/elrond/UnbalanceSet.ml";
  [%expect {|
    passing: unbalanced_set_gen
    failing:
  |}]

let%expect_test "elrond/stream" =
  run_test "data/PLDI23/elrond/stream.ml";
  [%expect {|
    passing: stream_gen
    failing:
  |}]

let%expect_test "elrond/BankersQueue" =
  run_test "data/PLDI23/elrond/BankersQueue.ml";
  [%expect {|
    passing: bankersq_gen
    failing:
  |}]

let%expect_test "quickcheck/SizedHeap" =
  run_test "data/PLDI23/quickcheck/SizedHeap.ml";
  [%expect {|
    passing: depth_heap_gen
    failing:
  |}]

let%expect_test "alias" =
  run_test "data/inline_test/alias.ml";
  [%expect {|
    passing: 
    failing:
  |}]

let%expect_test "simple/ReturnError" =
  run_test "data/simple/ReturnError.ml";
  [%expect {|
    passing:
    failing: sized_list_gen
  |}]
