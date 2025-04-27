let rec bound_list_gen (size : int) (x : int) : int list =
  if size == 0 then []
  else
    let (y : int) = int_gen () in
    if x <= y then y :: bound_list_gen (size - 1) x else Err

let[@assert] bound_list_gen ?r:(s = ((0 <= v : [%v: int]) [@over])) ?r:(x : int)
    =
  (len v s && fun (u : int) -> implies (list_mem v u) (x <= u)
    : [%v: int list])
    [@under]
