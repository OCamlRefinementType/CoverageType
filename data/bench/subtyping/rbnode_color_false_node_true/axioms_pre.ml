let[@axiom] no_red_red_given_lt_rt_red_root (v : int rbtree) (lt : int rbtree) (rt : int rbtree) =
  (no_red_red lt && no_red_red rt && rb_lch v lt && rb_rch v rt
  && (not (rb_root_color lt true))
  && (not (rb_root_color rt true))
  && rb_root_color v true) #==> (no_red_red v)
