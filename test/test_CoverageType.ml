type test = {
  source_file : string;
  passing_tasks : string list;
  failing_tasks : string list;
}

let equal_ignore_order xs ys =
  List.sort String.compare xs = List.sort String.compare ys

let run_test { source_file; passing_tasks; failing_tasks } =
  let root = Filename.concat (Sys.getcwd ()) "../../../../.." in
  let _ =
    Myconfig.meta_config_path := Filename.concat root "test/meta-config.json"
  in
  let source_file = Filename.concat root source_file in
  Printf.printf "Running test on %s...\n" source_file;
  let code = Preprocess.preproress [ source_file ] in
  let _, passed, failed = Typing.struc_check (Preprocess.load_bctx ()) code in
  Printf.printf "Passed tasks: %s\n" (String.concat ", " passed);
  Printf.printf "Failed tasks: %s\n" (String.concat ", " failed);
  equal_ignore_order passed passing_tasks
  && equal_ignore_order failed failing_tasks

let%test "inline_test/alias" =
  run_test
    {
      source_file = "data/inline_test/alias.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "test_cases/basic_int" =
  run_test
    {
      source_file = "data/test_cases/basic_int.ml";
      passing_tasks = [ "test1"; "test3" ];
      failing_tasks = [];
    }

(* TODO: fix the test, need definitions for num_arr? *)
(* let%test "stlc/gen_term_size" = *)
(*   run_test *)
(*     { *)
(*       source_file = "data/PLDI23/stlc/gen_term_size.ml"; *)
(*       passing_tasks = [ "gen_term_size" ]; *)
(*       failing_tasks = []; *)
(*     } *)

(* sometimes fails, not sure why... some kind of nondeterminism *)
(* let%test "stlc/stlc" = *)
(*   run_test *)
(*     { *)
(*       source_file = "data/PLDI23/stlc/stlc.ml"; *)
(*       passing_tasks = *)
(*         [ *)
(*           "type_eq"; *)
(*           "gen_const"; *)
(*           "gen_type_size"; *)
(*           "gen_type"; *)
(*           "vars_with_type_rev_index"; *)
(*           "vars_with_type"; *)
(*           "gen_term_no_app"; *)
(*           "gen_term_size"; *)
(*         ]; *)
(*       failing_tasks = []; *)
(*     } *)

let%test "basic/duplicate_list" =
  run_test
    {
      source_file = "data/PLDI23/basic/duplicate_list.ml";
      passing_tasks = [ "duplicate_list_gen" ];
      failing_tasks = [];
    }

let%test "basic/sortedlist_simpl" =
  run_test
    {
      source_file = "data/PLDI23/basic/sortedlist_simpl.ml";
      passing_tasks = [ "sorted_list_gen" ];
      failing_tasks = [];
    }

let%test "basic/boundlist" =
  run_test
    {
      source_file = "data/PLDI23/basic/boundlist.ml";
      passing_tasks = [ "bound_list_gen" ];
      failing_tasks = [];
    }

let%test "quickchick/SizedTree" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SizedTree.ml";
      passing_tasks = [ "depth_tree_gen" ];
      failing_tasks = [];
    }

let%test "quickchick/SizedList" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SizedList.ml";
      passing_tasks = [ "sized_list_gen" ];
      failing_tasks = [];
    }

let%test "quickchick/RedBlackTree" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/RedBlackTree.ml";
      passing_tasks = [ "rbtree_gen" ];
      failing_tasks = [];
    }

let%test "quickchick/SortedList" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SortedList.ml";
      passing_tasks = [ "sorted_list_gen" ];
      failing_tasks = [];
    }

let%test "leonidas/SizedBST" =
  run_test
    {
      source_file = "data/PLDI23/leonidas/SizedBST.ml";
      passing_tasks = [ "size_bst_gen" ];
      failing_tasks = [];
    }

let%test "leonidas/CompleteTree" =
  run_test
    {
      source_file = "data/PLDI23/leonidas/CompleteTree.ml";
      passing_tasks = [ "complete_tree_gen" ];
      failing_tasks = [];
    }

let%test "elrond/BatchedQueue" =
  run_test
    {
      source_file = "data/PLDI23/elrond/BatchedQueue.ml";
      passing_tasks = [ "batchedq_gen" ];
      failing_tasks = [];
    }

let%test "elrond/UniqueList" =
  run_test
    {
      source_file = "data/PLDI23/elrond/UniqueList.ml";
      passing_tasks = [ "unique_list_gen" ];
      failing_tasks = [];
    }

let%test "elrond/LeftistHeap" =
  run_test
    {
      source_file = "data/PLDI23/elrond/LeftistHeap.ml";
      passing_tasks = [ "leftisthp_gen" ];
      failing_tasks = [];
    }

let%test "elrond/UnbalanceSet" =
  run_test
    {
      source_file = "data/PLDI23/elrond/UnbalanceSet.ml";
      passing_tasks = [ "unbalanced_set_gen" ];
      failing_tasks = [];
    }

let%test "elrond/stream" =
  run_test
    {
      source_file = "data/PLDI23/elrond/stream.ml";
      passing_tasks = [ "stream_gen" ];
      failing_tasks = [];
    }

let%test "elrond/BankersQueue" =
  run_test
    {
      source_file = "data/PLDI23/elrond/BankersQueue.ml";
      passing_tasks = [ "bankersq_gen" ];
      failing_tasks = [];
    }

let%test "quickcheck/SizedHeap" =
  run_test
    {
      source_file = "data/PLDI23/quickcheck/SizedHeap.ml";
      passing_tasks = [ "depth_heap_gen" ];
      failing_tasks = [];
    }

let%test "quickcheck/SizedSet" =
  run_test
    {
      source_file = "data/PLDI23/quickcheck/SizedSet.ml";
      passing_tasks = [ "ranged_set_gen" ];
      failing_tasks = [];
    }

let%test "alias" =
  run_test
    {
      source_file = "data/inline_test/alias.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "vellvm" =
  run_test
    {
      source_file = "data/monad/vellvm.ml";
      passing_tasks = [ "gen_uvalue" ];
      failing_tasks = [];
    }

let%test "coverage_monad_library" =
  run_test
    {
      source_file = "data/monad/coverage_monad_library.ml";
      passing_tasks =
        [
          "return";
          "bind";
          "fmap";
          "fmap2";
          "union";
          "fix";
          "int_bound";
          "int_range";
          "nat";
          "pair";
          "option";
          "oneof";
          "nil_gen";
          "cons_gen";
          "oneofl";
          "frequencyl_aux";
          "frequencyl";
          "frequency";
          "numeral";
          "list_repeat";
          "pos_split2";
        ];
      failing_tasks = [];
    }

let%test "tezos" =
  run_test
    {
      source_file = "data/monad/tezos.ml";
      passing_tasks =
        [ "operation_proto_gen"; "q_in_0_1"; "priority_gen"; "tezos_tree_gen" ];
      failing_tasks = [];
    }

let%test "case1" =
  run_test
    {
      source_file = "data/monad/case1.ml";
      passing_tasks = [ "union" ];
      failing_tasks = [];
    }

let%test "xen_api" =
  run_test
    {
      source_file = "data/monad/xen_api.ml";
      passing_tasks =
        [
          "fd_size_gen";
          "file_kind_gen";
          "timeout_gen";
          "total_delay_gen";
          "size_bound_gen";
          "testable_file_kind_gen";
          "select_fd_spec_gen";
          "file_list_gen";
          "fd_gen";
        ];
      failing_tasks = [];
    }

let%test "zipperposition" =
  run_test
    {
      source_file = "data/monad/zipperposition.ml";
      passing_tasks = [ "default_fuel" ];
      failing_tasks = [];
    }

let%test "herdtools7" =
  run_test
    {
      source_file = "data/monad/herdtools7.ml";
      passing_tasks = [ "literal" ];
      failing_tasks = [];
    }

let%test "test" =
  run_test
    {
      source_file = "data/monad/test.ml";
      passing_tasks = [ "return" ];
      failing_tasks = [];
    }

let%test "tree2list" =
  run_test
    {
      source_file = "data/monad/tree2list.ml";
      passing_tasks = [ "flatten"; "list_gen" ];
      failing_tasks = [];
    }

let%test "tezos_test" =
  run_test
    {
      source_file = "data/monad/tezos_test.ml";
      passing_tasks = [ "operation_proto_gen"; "q_in_0_1"; "priority_gen" ];
      failing_tasks = [];
    }
