open Ppx_compare_lib.Builtin
open Sexplib.Std

type test = {
  source_file : string;
  passing_tasks : string list;
  failing_tasks : string list;
}

let run_test { source_file; passing_tasks; failing_tasks } =
  Statistic.clear ();
  let root = Filename.concat (Sys.getcwd ()) "../../../../.." in
  let _ =
    Myconfig.meta_config_path := Filename.concat root "test/meta-config.json"
  in
  let source_file = Filename.concat root source_file in
  let code = Preprocess.preproress [ source_file ] in
  let _, passed, failed = Typing.struc_check (Preprocess.load_bctx ()) code in
  [%test_eq: string list] passing_tasks passed;
  [%test_eq: string list] failing_tasks failed

let%test_unit "inline_test/alias" =
  run_test
    {
      source_file = "data/inline_test/alias.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test_unit "test_cases/basic_int" =
  run_test
    {
      source_file = "data/test_cases/basic_int.ml";
      passing_tasks = [ "test1" ];
      failing_tasks = [ "test3" ];
    }

(* TODO: fix the test, need definitions for num_arr? *)
(* let%test_unit "stlc/gen_term_size" = *)
(*   run_test *)
(*     { *)
(*       source_file = "data/PLDI23/stlc/gen_term_size.ml"; *)
(*       passing_tasks = [ "gen_term_size" ]; *)
(*       failing_tasks = []; *)
(*     } *)

(* sometimes fails, not sure why... some kind of nondeterminism *)
(* let%test_unit "stlc/stlc" = *)
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

let%test_unit "basic/duplicate_list" =
  run_test
    {
      source_file = "data/PLDI23/basic/duplicate_list.ml";
      passing_tasks = [ "duplicate_list_gen" ];
      failing_tasks = [];
    }

let%test_unit "basic/sortedlist_simpl" =
  run_test
    {
      source_file = "data/PLDI23/basic/sortedlist_simpl.ml";
      passing_tasks = [ "sorted_list_gen" ];
      failing_tasks = [];
    }

let%test_unit "basic/boundlist" =
  run_test
    {
      source_file = "data/PLDI23/basic/boundlist.ml";
      passing_tasks = [ "bound_list_gen" ];
      failing_tasks = [];
    }

let%test_unit "quickchick/SizedTree" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SizedTree.ml";
      passing_tasks = [ "depth_tree_gen" ];
      failing_tasks = [];
    }

let%test_unit "quickchick/SizedList" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SizedList.ml";
      passing_tasks = [ "sized_list_gen" ];
      failing_tasks = [];
    }

let%test_unit "quickchick/RedBlackTree" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/RedBlackTree.ml";
      passing_tasks = [ "rbtree_gen" ];
      failing_tasks = [];
    }

let%test_unit "quickchick/SortedList" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SortedList.ml";
      passing_tasks = [ "sorted_list_gen" ];
      failing_tasks = [];
    }

let%test_unit "leonidas/SizedBST" =
  run_test
    {
      source_file = "data/PLDI23/leonidas/SizedBST.ml";
      passing_tasks = [ "size_bst_gen" ];
      failing_tasks = [];
    }

let%test_unit "leonidas/CompleteTree" =
  run_test
    {
      source_file = "data/PLDI23/leonidas/CompleteTree.ml";
      passing_tasks = [ "complete_tree_gen" ];
      failing_tasks = [];
    }

let%test_unit "elrond/BatchedQueue" =
  run_test
    {
      source_file = "data/PLDI23/elrond/BatchedQueue.ml";
      passing_tasks = [ "batchedq_gen" ];
      failing_tasks = [];
    }

let%test_unit "elrond/UniqueList" =
  run_test
    {
      source_file = "data/PLDI23/elrond/UniqueList.ml";
      passing_tasks = [ "unique_list_gen" ];
      failing_tasks = [];
    }

let%test_unit "elrond/LeftistHeap" =
  run_test
    {
      source_file = "data/PLDI23/elrond/LeftistHeap.ml";
      passing_tasks = [ "leftisthp_gen" ];
      failing_tasks = [];
    }

let%test_unit "elrond/UnbalanceSet" =
  run_test
    {
      source_file = "data/PLDI23/elrond/UnbalanceSet.ml";
      passing_tasks = [ "unbalanced_set_gen" ];
      failing_tasks = [];
    }

let%test_unit "elrond/stream" =
  run_test
    {
      source_file = "data/PLDI23/elrond/stream.ml";
      passing_tasks = [ "stream_gen" ];
      failing_tasks = [];
    }

let%test_unit "elrond/BankersQueue" =
  run_test
    {
      source_file = "data/PLDI23/elrond/BankersQueue.ml";
      passing_tasks = [ "bankersq_gen" ];
      failing_tasks = [];
    }

let%test_unit "quickcheck/SizedHeap" =
  run_test
    {
      source_file = "data/PLDI23/quickcheck/SizedHeap.ml";
      passing_tasks = [ "depth_heap_gen" ];
      failing_tasks = [];
    }

let%test_unit "quickcheck/SizedSet" =
  run_test
    {
      source_file = "data/PLDI23/quickcheck/SizedSet.ml";
      passing_tasks = [ "ranged_set_gen" ];
      failing_tasks = [];
    }

let%test_unit "alias" =
  run_test
    {
      source_file = "data/inline_test/alias.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test_unit "coverage_monad_library" =
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

let%test_unit "case1" =
  run_test
    {
      source_file = "data/monad/case1.ml";
      passing_tasks = [ "union" ];
      failing_tasks = [];
    }

(*
let%test_unit "tezos" =
  run_test
    {
      source_file = "data/monad/tezos.ml";
      passing_tasks =
        [ "operation_proto_gen"; "q_in_0_1"; "priority_gen"; "tezos_tree_gen" ];
      failing_tasks = [];
    }

let%test_unit "vellvm" =
  run_test
    {
      source_file = "data/monad/vellvm.ml";
      passing_tasks = [ "gen_uvalue" ];
      failing_tasks = [];
    }

let%test_unit "xen_api" =
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

let%test_unit "zipperposition" =
  run_test
    {
      source_file = "data/monad/zipperposition.ml";
      passing_tasks = [ "default_fuel" ];
      failing_tasks = [];
    }

let%test_unit "herdtools7" =
  run_test
    {
      source_file = "data/monad/herdtools7.ml";
      passing_tasks = [ "literal" ];
      failing_tasks = [];
    }

let%test_unit "test" =
  run_test
    {
      source_file = "data/monad/test.ml";
      passing_tasks = [ "return" ];
      failing_tasks = [];
    }

let%test_unit "tree2list" =
  run_test
    {
      source_file = "data/monad/tree2list.ml";
      passing_tasks = [ "flatten"; "list_gen" ];
      failing_tasks = [];
    }

let%test_unit "tezos_test" =
  run_test
    {
      source_file = "data/monad/tezos_test.ml";
      passing_tasks = [ "operation_proto_gen"; "q_in_0_1"; "priority_gen" ];
      failing_tasks = [];
    }
*)

let%test_unit "simple/ReturnError" =
  run_test
    {
      source_file = "data/simple/ReturnError.ml";
      passing_tasks = [];
      failing_tasks = [ "sized_list_gen" ];
    }
