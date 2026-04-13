let[@axiom] tree_no_leaf_exists_lch = fun (l : (int tree)) -> fun ((l1 [@ex]) : (int tree)) -> ((not (leaf l)) #==> (lch l l1))
let[@axiom] tree_no_leaf_exists_rch = fun (l : (int tree)) -> fun ((l1 [@ex]) : (int tree)) -> ((not (leaf l)) #==> (rch l l1))
let[@axiom] tree_no_leaf_exists_root = fun (l : (int tree)) -> fun ((x [@ex]) : int) -> ((not (leaf l)) #==> (root l x))
let[@axiom] tree_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
  (lch l l1 && depth l n && depth l1 n1) #==> (n1 <= n - 1)
let[@axiom] tree_rch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int) (n1 : int) =
  (rch l l1 && depth l n && depth l1 n1) #==> (n1 <= n - 1)
