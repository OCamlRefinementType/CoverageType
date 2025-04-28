let rec sized_list_gen (s : int) : int list =
  if s == 0 then []
  else if bool_gen () then []
  else int_gen () :: sized_list_gen (s - 1)

let[@assert] sized_list_gen ?r:(s = ((0 <= v : [%v: int]) [@over])) =
  (list_len v <= s : [%v: int list])
