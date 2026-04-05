
let[@axiom] tree_complete_lch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int) =
  (lch l l1 && complete l && depth l n) #==> (depth l1 (n - 1))

let[@axiom] tree_complete_rch_depth_minus_1 (l : int tree) (l1 : int tree) (n : int) =
  (rch l l1 && complete l && depth l n) #==> (depth l1 (n - 1))
