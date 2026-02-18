(** int list *)

(** basic *)

let[@axiom] list_emp_no_hd (l : int list) (x : int) =
  (emp l) #==> (not (hd l x))

let[@axiom] list_emp_no_tl (l : int list) (l1 : int list) =
  (emp l) #==> (not (tl l l1))

let[@axiom] list_no_emp_exists_tl (l : int list) ((l1 [@exists]) : int list) =
  (not (emp l)) #==> (tl l l1)

let[@axiom] list_no_emp_exists_hd (l : int list) ((x [@exists]) : int) =
  (not (emp l)) #==> (hd l x)

let[@axiom] list_hd_no_emp (l : int list) (x : int) =
  (hd l x) #==> (not (emp l))

let[@axiom] list_tl_no_emp (l : int list) (l1 : int list) =
  (tl l l1) #==> (not (emp l))

(** len *)

let[@axiom] list_len_geq_0 (l : int list) (n : int) = (len l n) #==> (n >= 0)
let[@axiom] list_len_0_emp (l : int list) = (emp l) #==> (len l 0)

let[@axiom] list_emp_len_0 (l : int list) (n : int) =
  (emp l && len l n) #==> (n == 0)

let[@axiom] list_positive_len_is_not_emp (l : int list) (n : int) =
  (len l n && n > 0) #==> (not (emp l))

let[@axiom] list_tl_len_plus_1 (l : int list) (l1 : int list) (n : int) =
  (tl l l1) #==> (iff (len l1 n) (len l (n + 1)))

(** list_mem *)

let[@axiom] list_hd_is_mem (l : int list) (u : int) =
  (hd l u) #==> (list_mem l u)

let[@axiom] list_emp_no_mem (l : int list) (u : int) =
  (emp l) #==> (not (list_mem l u))

let[@axiom] list_tl_mem (l : int list) (l1 : int list) (u : int) =
  (tl l l1 && list_mem l1 u) #==> (list_mem l u)

let[@axiom] list_cons_mem (l : int list) (l1 : int list) (u : int) =
  (tl l l1 && list_mem l u) #==> (list_mem l1 u || hd l u)

(** sorted *)

let[@axiom] list_emp_sorted (l : int list) = (emp l) #==> (sorted l)

let[@axiom] list_tl_sorted (l : int list) (l1 : int list) =
  (tl l l1 && sorted l) #==> (sorted l1)

let[@axiom] list_hd_sorted (l : int list) (l1 : int list) (x : int) (y : int) =
  (tl l l1 && sorted l) #==> (emp l1 || ((hd l1 y && hd l x) #==> (x <= y)))

(** unique *)

let[@axiom] list_emp_unique (l : int list) = (emp l) #==> (uniq l)

let[@axiom] list_tl_unique (l : int list) (l1 : int list) =
  (tl l l1 && uniq l) #==> (uniq l1)

let[@axiom] list_hd_unique (l : int list) (l1 : int list) (x : int) =
  (tl l l1 && uniq l && hd l1 x) #==> (not (list_mem l1 x))

(** int tree *)

(** basic *)

let[@axiom] tree_leaf_no_root (l : int tree) (x : int) =
  (leaf l) #==> (not (root l x))

let[@axiom] tree_leaf_no_ch (l : int tree) (l1 : int tree) =
  (leaf l) #==> (not (lch l l1 || rch l l1))

let[@axiom] tree_no_leaf_exists_ch (l : int tree) ((l1 [@exists]) : int tree)
    ((l2 [@exists]) : int tree) =
  (not (leaf l)) #==> (lch l l1 && rch l l2)

let[@axiom] tree_no_leaf_exists_root (l : int tree) ((x [@exists]) : int) =
  (not (leaf l)) #==> (root l x)

let[@axiom] tree_root_no_leaf (l : int tree) (x : int) =
  (root l x) #==> (not (leaf l))

let[@axiom] tree_ch_no_leaf (l : int tree) (l1 : int tree) =
  (lch l l1 || rch l l1) #==> (not (leaf l))

(** depth *)

let[@axiom] tree_depth_geq_0 (l : int tree) (n : int) = (depth l n) #==> (n >= 0)

let[@axiom] tree_leaf_depth_0 (l : int tree) (n : int) =
  (leaf l && depth l n) #==> (n == 0)

let[@axiom] tree_positive_depth_is_not_leaf (l : int tree) (n : int) =
  (depth l n && n > 0) #==> (not (leaf l))

let[@axiom] tree_ch_depth_ex (l : int tree) (l1 : int tree) (n : int)
    ((n1 [@exists]) : int) =
  ((lch l l1 || rch l l1) && depth l n) #==> (depth l1 n1)

let[@axiom] tree_ch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int)
    (n1 : int) =
  ((lch l l1 || rch l l1) && depth l n && depth l1 n1) #==> (n1 <= n - 1)

let[@axiom] tree_depth_0_is_leaf (l : int tree) (n : int) =
  (depth l n && n == 0) #==> (leaf l)

(** tree_mem *)

let[@axiom] tree_root_mem (l : int tree) (x : int) =
  (root l x) #==> (tree_mem l x)

let[@axiom] tree_mem_lch_mem (l : int tree) (l1 : int tree) (x : int) =
  (lch l l1 && tree_mem l1 x) #==> (tree_mem l x)

let[@axiom] tree_mem_rch_mem (l : int tree) (l1 : int tree) (x : int) =
  (rch l l1 && tree_mem l1 x) #==> (tree_mem l x)

(** bst *)

let[@axiom] tree_leaf_bst (l : int tree) = (leaf l) #==> (bst l)

let[@axiom] tree_bst_lch_bst (l : int tree) (l1 : int tree) =
  (lch l l1 && bst l) #==> (bst l1)

let[@axiom] tree_bst_rch_bst (l : int tree) (l1 : int tree) =
  (rch l l1 && bst l) #==> (bst l1)

let[@axiom] tree_bst_lch_mem_lt_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && lch l l1 && root l x && tree_mem l1 y) #==> (y < x)

let[@axiom] tree_bst_rch_mem_gt_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (bst l && rch l l1 && root l x && tree_mem l1 y) #==> (x < y)

(** heap *)

let[@axiom] tree_heap_lch_heap (l : int tree) (l1 : int tree) =
  (lch l l1 && heap l) #==> (heap l1)

let[@axiom] tree_heap_rch_heap (l : int tree) (l1 : int tree) =
  (rch l l1 && heap l) #==> (heap l1)

let[@axiom] tree_heap_root_lt_lch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && lch l l1 && root l x && root l1 y) #==> (y < x)

let[@axiom] tree_heap_root_rt_rch_root (l : int tree) (l1 : int tree) (x : int)
    (y : int) =
  (heap l && rch l l1 && root l x && root l1 y) #==> (y < x)

(** complete *)

let[@axiom] tree_complete_lch_complete (l : int tree) (l1 : int tree) =
  (lch l l1 && complete l) #==> (complete l1)

let[@axiom] tree_complete_rch_complete (l : int tree) (l1 : int tree) =
  (rch l l1 && complete l) #==> (complete l1)

let[@axiom] tree_complete_lch_depth_minus_1 (l : int tree) (l1 : int tree)
    (n : int) =
  (lch l l1 && complete l && depth l n) #==> (depth l1 (n - 1))

let[@axiom] tree_complete_rch_depth_minus_1 (l : int tree) (l1 : int tree)
    (n : int) =
  (rch l l1 && complete l && depth l n) #==> (depth l1 (n - 1))
