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

let%expect_test "test_cases/op_head" =
  run_test "data/test_cases/op_head.ml";
  [%expect {|
    passing: op_head_gen
    failing:
    |}]

let%expect_test "test_cases/record_pattern" =
  let layout_source str =
    match
      Language.ocaml_structure_to_items
        (Zutils.OcamlParser.Oparse.parse_imp str)
    with
    | items -> print_endline (Language.layout_item (List.nth items 1))
    | exception Failure msg ->
        (* Drop the "[file … line …]: " prefix, which moves on every edit. *)
        let i = String.index msg ']' + 3 in
        print_endline (String.sub msg i (String.length msg - i))
  in
  (* Fields written out of declaration order would bind to the wrong
     constructor arguments if matched by position. *)
  List.iter
    (fun case ->
      layout_source
        ("type rnode = RLeaf | RNode of { flag : bool; n : int }\n"
       ^ "let f (t : rnode) : bool = match t with " ^ case ^ " -> b"))
    [
      "RNode { flag = b; n = k }";
      "RNode { n = k; flag = b }";
      "RNode { flag = b }";
      "RNode { flag = b; _ }";
      "RNode { flag = b; m = k }";
    ];
  [%expect
    {|
    let f : rnode -> bool ? rnode -> bool = fun (t : rnode) -> (match t with | RNode (b, k) -> b : bool)
    let f : rnode -> bool ? rnode -> bool = fun (t : rnode) -> (match t with | RNode (b, k) -> b : bool)
    let f : rnode -> bool ? rnode -> bool = fun (t : rnode) -> (match t with | RNode (b, _) -> b : bool)
    let f : rnode -> bool ? rnode -> bool = fun (t : rnode) -> (match t with | RNode (b, _) -> b : bool)
    record pattern on RNode binds m; its declaration has {flag, n}
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

  let%test "rty source: existential base coverage type" =
    round_trips
      (rty_of_source
         "(((is_nil v) && (fun (((n)[@exists]) : int) -> (len v n) && (n <= \
          s))) : [%v : ilist]) [@under]")

  let%test "rty source: arrow" =
    round_trips (RtyArr { argrty = int_over; arg = "a"; retty = int_under })

  let%test "rty source: nested arrows" =
    round_trips
      (RtyArr
         {
           argrty = int_over;
           arg = "a";
           retty = RtyArr { argrty = int_over; arg = "b"; retty = int_under };
         })

  (* [M e] has no inverse: it parses to the [RtyArr] the renderer emits. *)
  let%test "rty source: monadic return" =
    round_trips (rty_of_source "M ((v >= 0 : [%v: int]) [@under])")

  let%test "rty source: optional-label argument" =
    round_trips
      (rty_of_source "fun ?(a : int) -> (v >= 0 : [%v: int]) [@under]")

  let%test "rty source: poly type" =
    round_trips (RtyPolyType { pt = "a"; rty = int_under })

  let%test "rty source: poly pred" =
    round_trips
      (RtyPolyPred
         { pred = "p"#:(Nt.mk_arr Nt.int_ty Nt.bool_ty); rty = int_under })
end
