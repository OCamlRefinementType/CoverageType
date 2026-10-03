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

let%expect_test "test_cases/closure_capture" =
  run_test "data/test_cases/pair_diagonal.ml";
  run_test "data/test_cases/closure_capture_pair.ml";
  [%expect
    {|
    passing:
    failing: diagonal
    passing: f, diagonal_via_closure
    failing:
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

(* TODO: fix the test, need definitions for num_arr? *)
(* let%expect_test "stlc/gen_term_size" = *)
(*   run_test "data/PLDI23/stlc/gen_term_size.ml"; *)
(*   [%expect {| *)
(*     passing:  gen_term_size  *)
(*     failing: *)
(*   |}] *)

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

module Rty_source = struct
  open Zutils
  open Sugar
  open Language

  (* The renderers read the global zutils config. *)
  let () = ZUtilsConfig.set (Result.get_ok (ZUtilsConfig.of_yojson (`Assoc [])))

  let round_trips r =
    equal_rty Nt.equal_nt r (rty_of_source (layout_rty_source r))

  let int_over = rty_of_source "(true : [%v: int]) [@over]"
  let int_under = rty_of_source "(v >= 0 : [%v: int]) [@under]"

  let%expect_test "rty source: existential base coverage type" =
    assert (
      round_trips
        (rty_of_source
           "(((is_nil v) && (fun (((n)[@exists]) : int) -> (len v n) && (n <= \
            s))) : [%v : ilist]) [@under]"))

  let%expect_test "rty source: arrow" =
    assert (
      round_trips (RtyArr { argrty = int_over; arg = "a"; retty = int_under }))

  let%expect_test "rty source: nested arrows" =
    assert (
      round_trips
        (RtyArr
           {
             argrty = int_over;
             arg = "a";
             retty = RtyArr { argrty = int_over; arg = "b"; retty = int_under };
           }))

  (* [M e] has no inverse: it parses to the [RtyArr] the renderer emits. *)
  let%expect_test "rty source: monadic return" =
    assert (round_trips (rty_of_source "M ((v >= 0 : [%v: int]) [@under])"))

  let%expect_test "rty source: optional-label argument" =
    assert (
      round_trips
        (rty_of_source "fun ?(a : int) -> (v >= 0 : [%v: int]) [@under]"))

  let%expect_test "rty source: poly type" =
    assert (round_trips (RtyPolyType { pt = "a"; rty = int_under }))

  let%expect_test "rty source: poly pred" =
    assert (
      round_trips
        (RtyPolyPred
           { pred = "p"#:(Nt.mk_arr Nt.int_ty Nt.bool_ty); rty = int_under }))
end
