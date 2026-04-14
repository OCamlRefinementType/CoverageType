let[@axiom] rbtree_no_rb_leaf_exists_ch = fun (l : (int rbtree)) -> fun ((l1 [@ex]) : (int rbtree)) ((l2 [@ex]) : (int rbtree)) -> ((not (rb_leaf l)) #==> ((rb_lch l l1) && (rb_rch l l2)))
let[@axiom] rbtree_no_rb_leaf_exists_rb_root_color (l : int rbtree) ((x [@exists]) : bool) =
  (not (rb_leaf l)) #==> (rb_root_color l x)

let[@axiom] black_lt_black_num_black_gt_1 (v : int rbtree) (lt : int rbtree) (h : int) =
  (num_black v h && rb_lch v lt && rb_root_color v false
 && rb_root_color lt false)#==>(h > 1)

let[@axiom] black_rt_black_num_black_gt_1 (v : int rbtree) (rt : int rbtree) (h : int) =
  (num_black v h && rb_rch v rt && rb_root_color v false
 && rb_root_color rt false)#==>(h > 1)