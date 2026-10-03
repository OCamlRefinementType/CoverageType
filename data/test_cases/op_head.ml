let op_head_gen (u : unit) : int =
  let (x : int) = int_gen () in
  if x = 0 then Err else x

let[@assert] op_head_gen ?l:(u = ((true : [%v: unit]) [@over])) =
  (v != 0 : [%v: int]) [@under]
