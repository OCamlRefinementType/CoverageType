(** We always use 'a as poly type in the axioms *)

(** Axioms *)

(** Rational *)

let[@axiom] rational_zero_one =
 fun (v : int * int) ->
  (rational_zero_one v)#==>(0 <= fst v
                           && fst v <= snd v
                           && 1 <= snd v
                           && snd v <= 2147483647)

(** Priority *)

let[@axiom] wf_priority =
 fun (v : priority) ->
  implies (wf_priority v) (fun ((x_17 [@exists]) : priority list) ->
      list_len x_17 == 0 && fun ((x_18 [@exists]) : (int * int) list) ->
      list_len x_18 == 0 && fun ((x_19 [@exists]) : priority) ->
      is_low x_19 x_18 && fun ((x_20 [@exists]) : priority list) ->
      hd x_20 x_19 && tl x_20 x_17
      && fun ((x_21 [@exists]) : priority) ->
      is_medium x_21 && fun ((x_22 [@exists]) : priority list) ->
      hd x_22 x_21 && tl x_22 x_20
      && fun ((x_23 [@exists]) : priority) ->
      is_high x_23 && fun ((x_24 [@exists]) : priority list) ->
      hd x_24 x_23 && tl x_24 x_22
      && fun ((x_44 [@exists]) : priority) ->
      list_mem x_24 x_44
      && ((is_high x_44 && is_high v)
         || (is_medium x_44 && is_medium v)
            && fun ((lowl [@exists]) : (int * int) list) ->
            is_low x_44 lowl && fun ((x_50 [@exists]) : (int * int) list) ->
            rational_zero_one_list x_50 && list_len x_50 <= 100 && is_low v x_50
         ))

(** Tezos *)

let[@axiom] tl_wf_decreasing =
 fun (l : 'a list) (ll : 'a list) -> (tl l ll)#==>(decreasing ll l)

let[@axiom] list_concat_wf_decreasing =
 fun (l : 'a list) (l1 : 'a list) (l2 : 'a list) ->
  (list_concat l1 l2 l)#==>(decreasing l1 l && decreasing l2 l)

let[@axiom] l2t_pre_singleton =
 fun (l : 'a list) (x : 'a) (xs : 'a list) (tr : 'a tezosTree) ->
  (l2t_pre l tr && hd l x && tl l xs)#==>(iff
                                            (list_len xs == 0)
                                            (tezos_leaf tr x))

let[@axiom] tezos =
 fun (blocks : 'a list) ->
  fun (v : 'a tezosTree) ->
   implies (l2t_pre blocks v) (fun ((x [@exists]) : 'a) ->
       fun ((xs [@exists]) : 'a list) ->
        hd blocks x && tl blocks xs
        && (list_len xs == 0
           || (fun ((x_127 [@exists]) : 'a tezosTree) ->
                l2t_pre xs x_127 && tezos_node1 v x x_127)
              && fun ((x_130 [@exists]) : int) ->
              0 <= list_len xs
              && 0 <= x_130
              && x_130 <= list_len xs
              && fun ((x_131 [@exists]) : 'a list * 'a list) ->
              0 <= x_130
              && x_130 <= list_len xs
              && list_concat (fst x_131) (snd x_131) xs
              && ( list_len (fst x_131) == 0
                 && ( (list_len (snd x_131) == 0 && tezos_leaf v x)
                    || fun ((x_133 [@exists]) : 'a tezosTree) ->
                      l2t_pre (snd x_131) x_133 && tezos_node1 v x x_133 )
                 || fun ((x_132 [@exists]) : 'a tezosTree) ->
                   l2t_pre (fst x_131) x_132
                   && ( (list_len (snd x_131) == 0 && tezos_node1 v x x_132)
                      || fun ((x_134 [@exists]) : 'a tezosTree) ->
                        l2t_pre (snd x_131) x_134 && tezos_node2 v x x_132 x_134
                      ) )))

(** String *)

let[@axiom] string_len_geq_zero = fun (l : string) -> string_len l >= 0

(** List *)

let[@axiom] list_mem_has_nth =
 fun (l : 'a list) (v : 'a) ->
  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->
  0 <= idx && idx < list_len l && list_nth_pred l idx v)

let[@axiom] list_snd_mem_none_when_len_0 =
 fun (l : (int * 'a) list) (v : 'a) ->
  (list_len l == 0)#==>(not (list_snd_mem l v))

let[@axiom] list_snd_mem_implies_len_gt_zero =
 fun (l : (int * 'a) list) (v : 'a) -> (list_snd_mem l v)#==>(list_len l > 0)

let[@axiom] list_len_gt_zero_implies_has_hd_tl =
 fun (l : 'a list) ->
  (list_len l > 0) #==> (fun ((hde [@ex]) : 'a) ((tle [@ex]) : 'a list) ->
  hd l hde && tl l tle)

let[@axiom] list_snd_mem_implies_snd_mem_hd_or_tl =
 fun (l : (int * 'a) list) (v : 'a) (hde : int * 'a) (tle : (int * 'a) list) ->
  (list_snd_mem l v && hd l hde && tl l tle)#==>(v == snd hde
                                                || list_snd_mem tle v)

let[@axiom] list_tl_len_minus_one =
 fun (l : 'a list) (tle : 'a list) ->
  (tl l tle)#==>(list_len l == 1 + list_len tle)

let[@axiom] list_hd_implies_len_gt_zero =
 fun (l : 'a list) (v : 'a) -> (hd l v)#==>(list_len l > 0)

let[@axiom] list_tl_implies_len_gt_zero =
 fun (l : 'a list) (tle : 'a list) -> (tl l tle)#==>(list_len l > 0)

let[@axiom] list_hd_is_mem =
 fun (l : 'a list) (v : 'a) -> (hd l v)#==>(list_mem l v)

let[@axiom] list_hd_unique =
 fun (l : 'a list) (x : 'a) (y : 'a) -> (hd l x && hd l y)#==>(x == y)

let[@axiom] list_tl_unique =
 fun (l : 'a list) (tle1 : 'a list) (tle2 : 'a list) ->
  (tl l tle1 && tl l tle2)#==>(tle1 == tle2)

let[@axiom] list_len_geq_zero = fun (l : 'a list) -> list_len l >= 0

(* let[@axiom] list_len_geq_zero_implies_list_ex = *)
(*  fun (n : int) -> (0 <= n) #==> (fun ((l [@ex]) : 'a list) -> list_len l == n) *)

let[@axiom] int_list_exists_0_9 =
 fun ((l0 [@ex]) : int list) ((l1 [@ex]) : int list) ((l2 [@ex]) : int list) ->
  tl l2 l1 && tl l1 l0 && list_len l0 == 0 && hd l1 1 && hd l2 9

(** List :: uniq *)

let[@axiom] unique_list_implies_hd_not_mem_in_tl =
 fun (l : int list) (x : int) (xs : int list) ->
  (uniq l && hd l x && tl l xs)#==>(uniq xs && not (list_mem xs x))

let[@axiom] unique_list_length_1_ex =
 fun ((l [@ex]) : int list) -> list_len l == 1 && uniq l

(** List :: sorted *)

let[@axiom] list_emp_sorted (l : int list) = (list_len l == 0)#==>(sorted l)

let[@axiom] list_tl_sorted (l : int list) (l1 : int list) =
  (tl l l1 && sorted l)#==>(sorted l1)

let[@axiom] list_hd_sorted (l : int list) (l1 : int list) (x : int) (y : int) =
  (tl l l1 && sorted l)#==>(list_len l1 == 0
                           || ((hd l1 y && hd l x)#==>(x <= y)))

(** Tree *)

let[@axiom] tree_leaf_no_root (l : int tree) (x : int) =
  (depth l == 0)#==>(not (root l x))

let[@axiom] tree_leaf_no_ch (l : int tree) (l1 : int tree) =
  (depth l == 0)#==>(not (lch l l1 || rch l l1))

let[@axiom] tree_no_leaf_exists_lch (l : int tree) ((l1 [@exists]) : int tree) =
  (not (depth l == 0))#==>(lch l l1)

let[@axiom] tree_no_leaf_exists_rch (l : int tree) ((l2 [@exists]) : int tree) =
  (not (depth l == 0))#==>(rch l l2)

let[@axiom] tree_no_leaf_exists_root (l : int tree) ((x [@exists]) : int) =
  (not (depth l == 0))#==>(root l x)

let[@axiom] tree_root_no_leaf (l : int tree) (x : int) =
  (root l x)#==>(not (depth l == 0))

let[@axiom] tree_ch_no_leaf (l : int tree) (l1 : int tree) =
  (lch l l1 || rch l l1)#==>(not (depth l == 0))

let[@axiom] tree_depth_geq_0 (l : int tree) (n : int) =
  (depth l == n)#==>(n >= 0)

let[@axiom] tree_ch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  (lch l l1 || rch l l1)#==>(depth l1 == depth l - 1)

(** tree_mem *)

let[@axiom] tree_root_mem (l : int tree) (x : int) =
  (root l x)#==>(tree_mem l x)

let[@axiom] tree_mem_lch_mem (l : int tree) (l1 : int tree) (x : int) =
  (lch l l1 && tree_mem l1 x)#==>(tree_mem l x)

let[@axiom] tree_mem_rch_mem (l : int tree) (l1 : int tree) (x : int) =
  (rch l l1 && tree_mem l1 x)#==>(tree_mem l x)

(** bst *)

let[@axiom] tree_leaf_bst (l : int tree) = (depth l == 0)#==>(bst l)

let[@axiom] tree_bst_lch_bst (l : int tree) (l1 : int tree) =
  (lch l l1 && bst l)#==>(bst l1)

let[@axiom] tree_bst_rch_bst (l : int tree) (l1 : int tree) =
  (rch l l1 && bst l)#==>(bst l1)

let[@axiom] tree_bst_lch_mem_lt_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && lch l l1 && root l x && tree_mem l1 y)#==>(y < x)

let[@axiom] tree_bst_rch_mem_gt_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && rch l l1 && root l x && tree_mem l1 y)#==>(x < y)

(* let[@axiom] list_emp_unique = *)
(*  fun (l : int list) -> (list_len l == 0)#==>(uniq l) *)

(* let[@axiom] unique_list_tl_unique_list = *)
(*  fun (l : int list) (l1 : int list) -> (tl l l1 && uniq l)#==>(uniq l1) *)

(* let[@axiom] unique_list_hd_not_mem = *)
(*  fun (l : int list) (l1 : int list) (x : int) -> *)
(*   (tl l l1 && uniq l && hd l1 x)#==>(not (list_mem l1 x)) *)

(** tree :: complete *)

let[@axiom] tree_complete_lch_complete (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l)#==>(complete l1)

let[@axiom] tree_complete_rch_complete (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l)#==>(complete l1)

let[@axiom] tree_complete_lch_depth_minus_1 (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l)#==>(depth l == depth l1 + 1)

let[@axiom] tree_complete_rch_depth_minus_1 (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l)#==>(depth l == depth l1 + 1)

(** tree :: heap *)

let[@axiom] tree_heap_lch_heap (l : int tree) (l1 : int tree) =
  (lch l l1 && heap l)#==>(heap l1)

let[@axiom] tree_heap_rch_heap (l : int tree) (l1 : int tree) =
  (rch l l1 && heap l)#==>(heap l1)

let[@axiom] tree_heap_root_lt_lch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && lch l l1 && root l x && root l1 y)#==>(y < x)

let[@axiom] tree_heap_root_rt_rch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && rch l l1 && root l x && root l1 y)#==>(y < x)

(** stream *)

let[@axiom] stream_stream_emp_no_stream_hd (l : int stream) (x : int) =
  (stream_len l == 0)#==>(not (stream_hd l x))

let[@axiom] stream_stream_emp_no_stream_tl (l : int stream)
    (l1 : int stream lazyty) =
  (stream_len l == 0)#==>(not (stream_tl l (forc l1)))

let[@axiom] stream_no_stream_emp_exists_stream_tl (l : int stream)
    ((l1 [@exists]) : int stream lazyty) =
  (not (stream_len l == 0))#==>(stream_tl l (forc l1))

let[@axiom] stream_no_stream_emp_exists_stream_hd (l : int stream)
    ((x [@exists]) : int) =
  (not (stream_len l == 0))#==>(stream_hd l x)

let[@axiom] stream_stream_hd_no_stream_emp (l : int stream) (x : int) =
  (stream_hd l x)#==>(not (stream_len l == 0))

let[@axiom] stream_stream_tl_no_stream_emp (l : int stream)
    (l1 : int stream lazyty) =
  (stream_tl l (forc l1))#==>(not (stream_len l == 0))

let[@axiom] stream_stream_len_geq_0 (l : int stream) = stream_len l >= 0

let[@axiom] stream_stream_tl_stream_len_plus_1 (l : int stream)
    (l1 : int stream) =
  (stream_tl l l1)#==>(stream_len l1 + 1 == stream_len l)

(** leafisthp *)

(** basic *)

let[@axiom] leftisthp_leftisthp_leaf_no_leftisthp_root (l : int leftisthp)
    (x : int) =
  (leftisthp_depth l == 0)#==>(not (leftisthp_root l x))

let[@axiom] leftisthp_leftisthp_leaf_no_ch (l : int leftisthp)
    (l1 : int leftisthp) =
  (leftisthp_depth l == 0)#==>(not (leftisthp_lch l l1 || leftisthp_rch l l1))

let[@axiom] leftisthp_leftisthp_leaf_no_rank (l : int leftisthp) (r : int) =
  (leftisthp_depth l == 0)#==>(not (leftisthp_rank l r))

let[@axiom] leftisthp_no_leftisthp_leaf_exists_leftisthp =
 fun (v : int leftisthp) ->
  (leftisthp_depth v > 0)
  #==>
  (fun ((lt [@exists]) : int leftisthp)
    ((r [@exists]) : int)
    ((_x_3 [@exists]) : int)
    ((rt [@exists]) : int leftisthp)
  ->
  leftisthp_lch v lt && leftisthp_rank v r && leftisthp_rch v rt
  && leftisthp_root v _x_3)

let[@axiom] leftisthp_leftisthp_root_no_leftisthp_leaf (l : int leftisthp)
    (x : int) =
  (leftisthp_root l x)#==>(not (leftisthp_depth l == 0))

let[@axiom] leftisthp_ch_no_leftisthp_leaf (l : int leftisthp)
    (l1 : int leftisthp) =
  (leftisthp_lch l l1 || leftisthp_rch l l1)#==>(not (leftisthp_depth l == 0))

let[@axiom] leftisthp_right_depth_leq_depth (l : int leftisthp) (r : int) =
  (leftisthp_rank l r)#==>(r <= leftisthp_depth l && 0 < r)

let[@axiom] leftisthp_right_depth_m1_depth (l : int leftisthp)
    (l1 : int leftisthp) (r : int) =
  (leftisthp_rch l l1 && leftisthp_rank l r)#==>(leftisthp_depth l1 == r - 1)

let[@axiom] leftisthp_leftisthp_depth_ch_leftisthp_depth_minus_1
    (tr : int leftisthp) (tr1 : int leftisthp) (n : int) =
  (leftisthp_lch tr tr1)#==>(leftisthp_depth tr == leftisthp_depth tr1 + 1)

let[@axiom] leftisthp_leftisthp_depth_geq_0 (l : int leftisthp) =
  leftisthp_depth l >= 0

(** rbtree *)

let[@axiom] rbtree_rb_leaf_no_rb_root (l : int rbtree) (x : int) =
  (rb_leaf l)#==>(not (rb_root l x))

let[@axiom] rbtree_rb_leaf_no_rb_root_color (l : int rbtree) (x : bool) =
  (rb_leaf l)#==>(not (rb_root_color l x))

let[@axiom] rbtree_rb_leaf_no_ch (l : int rbtree) (l1 : int rbtree) =
  (rb_leaf l)#==>(not (rb_lch l l1 || rb_rch l l1))

let[@axiom] rbtree_no_rb_leaf_exists_ch (l : int rbtree)
    ((l1 [@exists]) : int rbtree) ((l2 [@exists]) : int rbtree) =
  (not (rb_leaf l))#==>(rb_lch l l1 && rb_rch l l2)

let[@axiom] rbtree_no_rb_leaf_exists_rb_root (l : int rbtree)
    ((x [@exists]) : int) =
  (not (rb_leaf l))#==>(rb_root l x)

let[@axiom] rbtree_no_rb_leaf_exists_rb_root_color (l : int rbtree)
    ((x [@exists]) : bool) =
  (not (rb_leaf l))#==>(rb_root_color l x)

let[@axiom] rbtree_rb_root_no_rb_leaf (l : int rbtree) (x : int) =
  (rb_root l x)#==>(not (rb_leaf l))

let[@axiom] rbtree_rb_root_color_no_rb_leaf (l : int rbtree) (x : bool) =
  (rb_root_color l x)#==>(not (rb_leaf l))

let[@axiom] rbtree_ch_no_rb_leaf (l : int rbtree) (l1 : int rbtree) =
  (rb_lch l l1 || rb_rch l l1)#==>(not (rb_leaf l))

let[@axiom] rbtree_num_black_0_rb_leaf (l : int rbtree) =
  (num_black l == 0 && not (rb_root_color l true))#==>(rb_leaf l)

let[@axiom] rbtree_num_black_geq_0 (l : int rbtree) = num_black l >= 0

let[@axiom] rbtree_rb_leaf_num_black_0 (l : int rbtree) (n : int) =
  (rb_leaf l && num_black l == n)#==>(n == 0)

let[@axiom] rbtree_positive_num_black_is_not_rb_leaf (l : int rbtree) =
  (num_black l > 0)#==>(not (rb_leaf l))

let[@axiom] num_black_root_black_lt_minus_1 (v : int rbtree) (lt : int rbtree) =
  (rb_root_color v false && rb_lch v lt)#==>(1 + num_black lt == num_black v)

let[@axiom] num_black_root_black_rt_minus_1 (v : int rbtree) (rt : int rbtree) =
  (rb_root_color v false && rb_rch v rt)#==>(1 + num_black rt == num_black v)

let[@axiom] num_black_root_red_lt_same (v : int rbtree) (lt : int rbtree) =
  (rb_root_color v true && rb_lch v lt)#==>(num_black lt == num_black v)

let[@axiom] num_black_root_red_rt_same (v : int rbtree) (rt : int rbtree) =
  (rb_root_color v true && rb_rch v rt)#==>(num_black rt == num_black v)

let[@axiom] num_black_root_black_0_lt_leaf (v : int rbtree) (lt : int rbtree) =
  (num_black v == 0 && rb_lch v lt)#==>(rb_leaf lt)

let[@axiom] num_black_root_black_0_rt_leaf (v : int rbtree) (rt : int rbtree) =
  (num_black v == 0 && rb_rch v rt)#==>(rb_leaf rt)

let[@axiom] num_black_root_black_0_rt_red (v : int rbtree) (rt : int rbtree) =
  (num_black v == 0 && rb_rch v rt)#==>(rb_root_color v true)

let[@axiom] no_red_red_lt (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt)#==>(no_red_red lt)

let[@axiom] no_red_red_rt (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt)#==>(no_red_red rt)

let[@axiom] no_red_red_root_red_lt_not_red (v : int rbtree) (lt : int rbtree) =
  (no_red_red v && rb_lch v lt && rb_root_color v true)#==>(not
                                                              (rb_root_color lt
                                                                 true))

let[@axiom] no_red_red_root_red_rt_not_red (v : int rbtree) (rt : int rbtree) =
  (no_red_red v && rb_rch v rt && rb_root_color v true)#==>(not
                                                              (rb_root_color rt
                                                                 true))

let[@axiom] black_lt_black_num_black_gt_1 (v : int rbtree) (lt : int rbtree) =
  (rb_lch v lt && rb_root_color v false && rb_root_color lt false)#==>(num_black
                                                                         v > 1)

let[@axiom] black_rt_black_num_black_gt_1 (v : int rbtree) (rt : int rbtree) =
  (rb_rch v rt && rb_root_color v false && rb_root_color rt false)#==>(num_black
                                                                         v > 1)
