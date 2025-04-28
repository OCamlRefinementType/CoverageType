let rec depth_heap_gen (d : int) (mx : int) : int tree =
  if d == 0 then Leaf
  else if bool_gen () then Leaf
  else
    let (n : int) = int_gen () in
    if n < mx then
      let (lt : int tree) = depth_heap_gen (d - 1) n in
      let (rt : int tree) = depth_heap_gen (d - 1) n in
      Node (n, lt, rt)
    else Err

let[@assert] depth_heap_gen ?r:(d = ((0 <= v : [%v: int]) [@over]))
    ?r:(mx : int) =
  (heap v && depth v <= d && fun (u : int) -> (root v u)#==>(u < mx)
    : [%v: int tree])
    [@under]
