let[@axiom] rbtree_rb_leaf_num_black_0_second = fun (l : (int rbtree)) -> ((rb_leaf l) #==> (num_black l 0))
let[@axiom] rbtree_rb_leaf_no_rb_root_color = fun (l : (int rbtree)) (x : bool) -> ((rb_leaf l) #==> (not (rb_root_color l x)))
let[@axiom] rbtree_rb_leaf_no_red_red = fun (l : (int rbtree)) -> ((rb_leaf l) #==> (no_red_red l))
