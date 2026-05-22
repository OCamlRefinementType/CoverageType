open Zdatatype

let run_test source_file =
  Statistic.clear ();
  let root = Filename.concat (Sys.getcwd ()) "../../../../.." in
  let _ =
    Myconfig.meta_config_path := Filename.concat root "test/meta-config.json"
  in
  let source_file = Filename.concat root source_file in
  let code = Preprocess.preprocess [ source_file ] in
  let _, passed, failed = Typing.struc_check (Preprocess.load_bctx ()) code in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed)

(* TODO: fix the test, need definitions for num_arr? *)
(* let%expect_test "stlc/gen_term_size" = *)
(*   run_test "data/PLDI23/stlc/gen_term_size.ml"; *)
(*   [%expect {| *)
(*     passing:  gen_term_size  *)
(*     failing: *)
(*   |}] *)

(* flaky test *)
(* let%expect_test "stlc/stlc" = *)
(*   run_test "data/PLDI23/stlc/stlc.ml"; *)
(*   [%expect *)
(*     {| *)
(*     passing: type_eq, gen_const, gen_type_size, gen_type, vars_with_type_rev_index, vars_with_type, gen_term_no_app, gen_term_size *)
(*     failing: *)
(*   |}] *)

(* flaky test *)
(* let%expect_test "leonidas/SizedBST" = *)
(*   run_test "data/PLDI23/leonidas/SizedBST.ml"; *)
(*   [%expect {| *)
(*     passing: size_bst_gen *)
(*     failing: *)
(*   |}] *)

(* flaky test *)
(* let%expect_test "elrond/LeftistHeap" = *)
(*   run_test "data/PLDI23/elrond/LeftistHeap.ml"; *)
(*   [%expect {| *)
(*     passing: leftisthp_gen *)
(*     failing: *)
(*   |}] *)

(* flaky test *)
(* let%expect_test "quickcheck/SizedSet" = *)
(*   run_test "data/PLDI23/quickcheck/SizedSet.ml"; *)
(*   [%expect {| *)
(*     passing: ranged_set_gen *)
(*     failing: *)
(*   |}] *)

let%expect_test "quickchick/SortedList" =
  run_test "data/PLDI23/quickchick/SortedList.ml";
  [%expect {|
    passing: sorted_list_gen
    failing:
  |}]

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

(*
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
*)
