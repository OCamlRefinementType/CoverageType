let[@library] int_range ?r:(a = ((true : [%v: int]) [@over]))
    ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

let rec ranged_set_gen (diff : int) (lo : int) (hi : int) : int tree =
  if hi <= 1 + lo then Leaf
  else if bool_gen () then Leaf
  else
    let (x : int) = int_range (lo + 1) (hi - 1) () in
    let (lt : int tree) = ranged_set_gen (x - lo) lo x in
    let (rt : int tree) = ranged_set_gen (hi - x) x hi in
    Node (x, lt, rt)

let[@assert] ranged_set_gen ?r:(d = ((0 <= v : [%v: int]) [@over]))
    ?r:(lo : int) ?r:(hi = ((v == lo + d : [%v: int]) [@over])) =
  ((fun (u : int) -> (tree_mem v u)#==>(lo < u && u < hi)) && bst v
    : [%v: int tree])
