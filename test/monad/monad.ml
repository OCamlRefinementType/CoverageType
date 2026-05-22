open Auxtest

let%expect_test "coverage_monad_library" =
  run_test "data/monad/coverage_monad_library.ml";
  [%expect
    {|
    passing: return, bind, fmap, fmap2, union, fix, int_bound, int_range, nat, pair, option, oneof, nil_gen, cons_gen, oneofl, frequencyl_aux, frequencyl, frequency, numeral, list_repeat, pos_split2
    failing:
  |}]

let%expect_test "case1" =
  run_test "data/monad/case1.ml";
  [%expect {|
    passing: union
    failing:
  |}]

let%expect_test "tezos" =
  run_test "data/monad/tezos.ml";
  [%expect
    {|
    passing: operation_proto_gen, q_in_0_1, priority_gen, tezos_tree_gen
    failing:
  |}]

let%expect_test "vellvm" =
  run_test "data/monad/vellvm.ml";
  [%expect {|
    passing: gen_uvalue
    failing:
  |}]

let%expect_test "xen_api" =
  run_test "data/monad/xen_api.ml";
  [%expect
    {|
    passing: fd_size_gen, file_kind_gen, timeout_gen, total_delay_gen, size_bound_gen, testable_file_kind_gen, select_fd_spec_gen, file_list_gen, fd_gen
    failing:
  |}]

let%expect_test "zipperposition" =
  run_test "data/monad/zipperposition.ml";
  [%expect {|
    passing: default_fuel
    failing:
  |}]

let%expect_test "herdtools7" =
  run_test "data/monad/herdtools7.ml";
  [%expect {|
    passing: literal
    failing:
  |}]

let%expect_test "test" =
  run_test "data/monad/test.ml";
  [%expect {|
    passing: return
    failing:
  |}]

let%expect_test "tree2list" =
  run_test "data/monad/tree2list.ml";
  [%expect {|
    passing: flattenlist_gen" ];
    failing:
  |}]

let%expect_test "tezos_test" =
  run_test "data/monad/tezos_test.ml";
  [%expect
    {|
    passing: operation_proto_gen, q_in_0_1, priority_gen
    failing:
  |}]
