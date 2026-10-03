let wildcard_match_gen (t : int tree) : int =
  let (x : int) = int_gen () in
  match t with
  | Leaf -> if x > 0 then x else Err
  | Node (_, _, _) -> if x > 0 then x else Err

let[@assert] wildcard_match_gen ?l:(t = ((true : [%v: int tree]) [@over])) =
  (0 < v : [%v: int]) [@under]
