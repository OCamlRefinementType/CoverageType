let[@library] int_range ?r:(a = ((true : [%v: int]) [@over]))
    ?r:(b = ((a <= v : [%v: int]) [@over])) =
  M (a <= v && v <= b : [%v: int])

let rec unbalanced_set_gen (d : int) (diff : int) (lo : int) (hi : int) :
    int tree =
  if d == 0 then Leaf
  else if bool_gen () then Leaf
  else if lo + 1 < hi then
    let (x : int) = int_range (lo + 1) (hi - 1) () in
    let (lt : int tree) = unbalanced_set_gen (d - 1) (x - lo) lo x in
    let (rt : int tree) = unbalanced_set_gen (d - 1) (hi - x) x hi in
    Node (x, lt, rt)
  else Err

let[@assert] unbalanced_set_gen ?r:(d = ((0 <= v : [%v: int]) [@over]))
    ?r:(diff : int) ?r:(lo : int) ?r:(hi = ((lo < v : [%v: int]) [@over])) =
  ((fun (u : int) -> (tree_mem v u)#==>(lo < u && u < hi))
   && bst v
   && depth v <= d
    : [%v: int tree])
