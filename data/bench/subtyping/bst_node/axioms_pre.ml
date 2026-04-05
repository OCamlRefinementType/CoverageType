let[@axiom] tree_depth_node_lch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n1 >= n2)
  #==> (depth l (n1 + 1))

let[@axiom] tree_depth_node_rch (l : int tree) (l1 : int tree) (l2 : int tree)
    (n1 : int) (n2 : int) =
  (depth l1 n1 && depth l2 n2 && lch l l1 && rch l l2 && n2 >= n1)
  #==> (depth l (n2 + 1))
