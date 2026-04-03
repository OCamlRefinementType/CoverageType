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
  equal_ignore_order passed passing_tasks
  && equal_ignore_order failed failing_tasks

let%test "alias" =
  run_test
    {
      source_file = "data/inline_test/alias.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

(*
let%test "basic_int" =
  run_test
    {
      source_file = "data/test_cases/basic_int.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "stlc/gen_term_size" =
  run_test
    {
      source_file = "data/PLDI23/stlc/gen_term_size.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "stlc/stlc" =
  run_test
    {
      source_file = "data/PLDI23/stlc/stlc.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "basic/duplicate_list" =
  run_test
    {
      source_file = "data/PLDI23/basic/duplicate_list.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "basic/sortedlist_simpl" =
  run_test
    {
      source_file = "data/PLDI23/basic/sortedlist_simpl.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "basic/boundlist" =
  run_test
    {
      source_file = "data/PLDI23/basic/boundlist.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "quickchick/SizedTree" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SizedTree.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "quickchick/SizedList" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SizedList.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "quickchick/RedBlackTree" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/RedBlackTree.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "quickchick/SortedList" =
  run_test
    {
      source_file = "data/PLDI23/quickchick/SortedList.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "leonidas/SizedBST" =
  run_test
    {
      source_file = "data/PLDI23/leonidas/SizedBST.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "leonidas/CompleteTree" =
  run_test
    {
      source_file = "data/PLDI23/leonidas/CompleteTree.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "elrond/BatchedQueue" =
  run_test
    {
      source_file = "data/PLDI23/elrond/BatchedQueue.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "elrond/UniqueList" =
  run_test
    {
      source_file = "data/PLDI23/elrond/UniqueList.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "elrond/LeftistHeap" =
  run_test
    {
      source_file = "data/PLDI23/elrond/LeftistHeap.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "elrond/UnbalanceSet" =
  run_test
    {
      source_file = "data/PLDI23/elrond/UnbalanceSet.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "elrond/stream" =
  run_test
    {
      source_file = "data/PLDI23/elrond/stream.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "elrond/BankersQueue" =
  run_test
    {
      source_file = "data/PLDI23/elrond/BankersQueue.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "quickcheck/SizedHeap" =
  run_test
    {
      source_file = "data/PLDI23/quickcheck/SizedHeap.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "quickcheck/SizedSet" =
  run_test
    {
      source_file = "data/PLDI23/quickcheck/SizedSet.ml";
      passing_tasks = [];
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
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "coverage_monad_library" =
  run_test
    {
      source_file = "data/monad/coverage_monad_library.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "tezos" =
  run_test
    {
      source_file = "data/monad/tezos.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "case1" =
  run_test
    {
      source_file = "data/monad/case1.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "xen_api" =
  run_test
    {
      source_file = "data/monad/xen_api.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "zipperposition" =
  run_test
    {
      source_file = "data/monad/zipperposition.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "herdtools7" =
  run_test
    {
      source_file = "data/monad/herdtools7.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "test" =
  run_test
    {
      source_file = "data/monad/test.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "tree2list" =
  run_test
    {
      source_file = "data/monad/tree2list.ml";
      passing_tasks = [];
      failing_tasks = [];
    }

let%test "tezos_test" =
  run_test
    {
      source_file = "data/monad/tezos_test.ml";
      passing_tasks = [];
      failing_tasks = [];
    }
*)
